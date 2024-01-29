'''
This module implements the functions necessary to learn from the verifier whether there
exist a port swap that can satisfy the spec.
If so, a counterexample is generated and analyzed to infer the correct connections.

Author: Antonio Iannopollo
'''

from pyco import LOG
from pyco.contract import CompositionMapping
from pycolite.formula import (Globally, Equivalence, Disjunction, Implication,
                              Negation, Conjunction, Next, TrueFormula, FalseFormula,
                                Constant, DoubleImplication, Eventually, Until, Le as Lt, Literal,
                                Geq, Leq, Ge as Gt, Addition)
from pycolite.symbol_sets import NusmvSymbolSet
from pycolite.types import FrozenInt, Int, FrozenBool, FrozenVar, Bool
from pycolite.nuxmv import (NuxmvRefinementStrategy, verify_tautology, verify_tautology_smv,
                            ltl2smv, _process_var_decl, MODULE_TEMPLATE, derive_valuation_from_trace,
                            trace_analysis_for_loc, build_module_from_trace, NuxmvPathLoader)
from pycolite.util.util import NUXMV_BOUND
from multiprocessing import *
from functools import reduce

def counterexample_analysis(spec_list, output_port_names, relevant_contracts, manager, pid, 
                            found_event, result_queue, terminate_evt):
    '''
    Analyze the model thorugh a series of counterexample to infer a set of connections which satisfies
    the spec, if one exists
    :param unconnected_spec:
    :param output_port_names:
    :param model:
    :param manager:
    :return:
    '''

    # LOG.debug('start')
    passed = None
    composition = None
    connected_spec = None
    contracts = None
    model_map = None
    preamble = None

    composition = None
    var_assign = {}
    original_spec = manager.spec

    print('*'),
    if terminate_evt.is_set():
        return False, composition, connected_spec, contracts, model_map

    (composition, spec_contract, rel_spec_ports,
     ref_formulas, all_specs_formula, neg_formula,
     preamble, guaranteed_if_used,
     var_map, lev_map, location_vars, location_map,
     parameters) = process_model(spec_list, output_port_names, relevant_contracts, manager)

    input_variables = set([p for p in list(spec_contract.input_ports_dict.values())])
    input_variables = input_variables & rel_spec_ports


    #performs first step of learning loo?p
    passed, candidate, var_assign, param_assign = exists_forall_learner(spec_contract, rel_spec_ports,
                                                          ref_formulas, all_specs_formula,
                                                          neg_formula,
                                                          preamble, guaranteed_if_used,
                                                        var_map, lev_map, input_variables,
                                                          location_vars, location_map,
                                                          terminate_evt, parameters, output_port_names,
                                                            max_depth=manager.max_depth)
    # LOG.debug(passed)

    if not passed:
        #nope, not found
        LOG.debug('nope')
        # assert False
        # return False, composition, connected_spec, contracts, model_map
        return None, None

    # convert names in spec to original spec
    for name, port in list(spec_contract.ports_dict.items()):
        uname = port.unique_name
        orig_port = original_spec.ports_dict[name]

        if uname in var_assign:
            var_assign[orig_port.base_name] = var_assign[uname]
            var_assign.pop(uname)
        else:
            for name in var_assign:
                if uname == var_assign[name]:
                    var_assign[name] = orig_port.base_name


    #convert params to unique names
    param_assign = {x.unique_name: v for x, v in list(param_assign.items())}

    # LOG.debug('spec done')
    # LOG.debug(model)
    LOG.debug(var_assign)
    LOG.debug(candidate)
    LOG.debug(param_assign)

    # if passed:
    #     LOG.debug('done')
    #     result_queue.put((pid, frozenset(var_assign.items()), frozenset(param_assign.items())))
    #     found_event.set()
    #     terminate_evt.set()

    return var_assign, param_assign


def extract_model_connections(spec_contract, relevant_contracts, output_port_names, library, manager):
    '''
    Extract possible connections form model
    :return:
    '''

    #build dict with ports and possible connections

    var_map = {}

    #create contract level variables(use contract names)
    component_map = {}

    #let's start with the spec
    for name in output_port_names:
        s_port = spec_contract.ports_dict[name]
        var_map[s_port] = set()
        #only output for spec

        for c in relevant_contracts:
            for oport in list(c.output_ports_dict.values()):

                if library.check_connectivity(s_port, oport):
                    var_map[s_port].add(oport)

    #now inter contract connections
    for ci in relevant_contracts:
        component_map[ci] = Literal(ci.unique_name.lower(), l_type=FrozenInt())
        for iport in list(ci.input_ports_dict.values()):
            var_map[iport] = set()

            for co in relevant_contracts - {ci}:
                for oport in list(co.output_ports_dict.values()):

                    if library.check_connectivity(iport, oport):
                        var_map[iport].add(oport)

            #and input specs
            for s_port in list(spec_contract.input_ports_dict.values()):
                if library.check_connectivity(iport, s_port):
                    var_map[iport].add(s_port)

    #LOG.debug(var_map)
    return var_map, component_map


def process_distinct_lib_ports(port1, port2, var_map):
    '''
    add a constraints to guarantee two ports are not connected to the same input
    :param component:
    :return:
    '''
    constraints = [TrueFormula()]

    if port1 in var_map and port2 in var_map:
        map1 = var_map[port1]
        map2 = var_map[port2]

        for conn in map1:
            inner = [FalseFormula()]
            left = Globally(Equivalence(port1.literal, conn.literal, merge_literals=False))
            for conn2 in map2 - {conn}:
                temp = Globally(Equivalence(port2.literal, conn2.literal, merge_literals=False))
                inner.append(temp)

            inner = reduce(lambda x,y: Disjunction(x, y, merge_literals=False), inner)

            constraints.append(Implication(left, inner, merge_literals=False))


    return reduce(lambda x,y: Conjunction(x, y, merge_literals=False), constraints)

def process_distinct_spec_ports(port1_name, port2_name, spec_contract, var_map):
    '''
    add a constraints to guarantee two ports are not connected to the same input
    :param component:
    :return:
    '''

    port1 = spec_contract.ports_dict[port1_name]
    port2 = spec_contract.ports_dict[port2_name]

    constraints = [TrueFormula()]
    if port1.is_output and port2.is_output:
        if port1 in var_map and port2 in var_map:
            map1 = var_map[port1]
            map2 = var_map[port2]
            for conn in map1:
                inner = [FalseFormula()]
                left = Globally(Equivalence(port1.literal, conn.literal, merge_literals=False))
                for conn2 in map2 - {conn}:
                    temp = Globally(Equivalence(port2.literal, conn2.literal, merge_literals=False))
                    inner.append(temp)

                inner = reduce(lambda x,y: Disjunction(x, y, merge_literals=False), inner)

                constraints.append(Implication(left, inner, merge_literals=False))

    if port1.is_input and port2.is_input:
        p1set = {p for p in var_map if port1 in var_map[p]}
        p2set = {p for p in var_map if port2 in var_map[p]}

        for p1 in p1set:
            inner = [FalseFormula()]
            left = Globally(Equivalence(p1.literal, port1.literal, merge_literals=False))
            for p2 in p2set - {p1}:
                temp = Globally(Equivalence(p2.literal, port2.literal, merge_literals=False))
                inner.append(temp)

            inner = reduce(lambda x,y: Disjunction(x, y, merge_literals=False), inner)

            constraints.append(Implication(left, inner, merge_literals=False))

    return reduce(lambda x,y: Conjunction(x, y, merge_literals=False), constraints)


def build_balance_constraints(balance_types, contracts, location_vars, location_map):
    '''
    returns constraints encoding balance constraints
    :param balance_types:
    :param location_vars:
    :param location_map:
    :return:
    '''
    #first phase, build map

    map_balance = {}

    for out_t, outqt_t, in_t, inqt_t in balance_types:
        temp_map = {}
        for c in contracts:
            temp_op = None
            temp_oq = None
            for op in list(c.output_ports_dict.values()):
                if c.port_type[op.base_name] == out_t:
                    temp_op = op
                if c.port_type[op.base_name] == outqt_t:
                    temp_oq = op

            if temp_op is not None and temp_oq is not None:
                temp_map[(temp_op, temp_oq)] = set()

        for c in contracts:
            temp_ip = None
            temp_qnt = None

            for ip in list(c.input_ports_dict.values()):
                if c.port_type[ip.base_name] == in_t:
                    temp_ip = ip
                    break

            for op in list(c.output_ports_dict.values()):
                if c.port_type[op.base_name] == inqt_t:
                    temp_qnt = op
                    break


            if temp_ip is not None and temp_qnt is not None:
                for k in temp_map:
                    temp_map[k].add((temp_ip, temp_qnt))

                map_balance.update(temp_map)

    #second phase, build formula
    all_c = []
    for (op, oq), setp in list(map_balance.items()):
        in_constr = []
        vlist = []
        for ip, iq in setp:
            if ip in location_vars:
                vq = Literal('q', l_type=FrozenInt())
                il = location_vars[ip]
                lval = [k for k,v in list(location_map[il].items()) if v == op]
                if len(lval) > 0:
                    lval = lval[0]

                    pos_p = Equivalence(il, Constant(lval), merge_literals=False)
                    pos_p = Implication(pos_p, Equivalence(vq, iq.literal, merge_literals=False), merge_literals=False)

                    neg_p = Negation(Equivalence(il, Constant(lval), merge_literals=False))
                    neg_p = Implication(neg_p, Equivalence(vq, Constant(0), merge_literals=False), merge_literals=False)

                    in_constr.append(Conjunction(pos_p, neg_p, merge_literals=False))
                    vlist.append(vq)

        if len(vlist) > 0:
            vsum = reduce(lambda x,y: Addition(x,y,merge_literals=False), vlist)
            vsum = Leq(vsum, oq.literal, merge_literals=False)

            in_constr.append(vsum)

            in_constr = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), in_constr)
            all_c.append(in_constr)


    all_f = None
    if len(all_c) > 0:
        all_f = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), all_c)

    LOG.debug(all_f)

    return all_f


def process_model(spec_list, output_port_names, relevant_contracts, manager):
    '''
    Build a SMV model and checks if there is any possible alternative set of connections to satisfy the spec.
    We first need to create additional formulas to express flexible connections.
    :return:
    '''

    # LOG.debug('IN')

    # LOG.debug(checked_variables)

    library = manager.library
    unconnected_spec = spec_list[0]
    spec_contract = unconnected_spec.copy()
    working_specs = {s.unique_name: s.copy() for s in spec_list}
    spec_dict = {s.unique_name: s for s in spec_list}
    parameters = {x.literal for c in relevant_contracts for x in list(c.output_ports_dict.values()) if isinstance(x.l_type, FrozenVar) and x in c.relevant_ports}

    parameters_by_contract = {}
    for c in relevant_contracts:
        p_set = set()

        for port in list(c.output_ports_dict.values()):
            if port.literal in parameters:
                p_set.add(port.literal)

        parameters_by_contract[c] = p_set

    #uniform specs
    for ws in list(spec_dict.values()):
        for port in list(ws.ports_dict.values()):
            name = port.base_name

            spec_contract.connect_to_port(spec_contract.ports_dict[name], port)

    # process working spec
    for ws in list(working_specs.values()):
        for port in list(ws.ports_dict.values()):
            name = port.base_name

            if name not in output_port_names:
                spec_contract.connect_to_port(spec_contract.ports_dict[name], port)

    #build single contract for working specs
    all_guarantees = reduce(lambda x,y: Conjunction(x, y, merge_literals=False),
                            [ws.guarantee_formula for ws in list(working_specs.values())])
    all_assumptions = reduce(lambda x,y: Conjunction(x, y, merge_literals=False),
                             [ws.assume_formula for ws in list(working_specs.values())])

    w_spec = list(working_specs.values())[0]
    w_spec.assume_formula = all_assumptions
    w_spec.guarantee_formula = all_guarantees

    #extend with fixed components
    for spec in list(spec_dict.values()):
        for c in manager.retrieve_fixed_components():
            spec.assume_formula = Conjunction(spec.assume_formula, c.assume_formula, merge_literals=False)

    rel_spec_ports = set()
    for spec in list(spec_dict.values()):
        rel_spec_ports |= spec.relevant_ports


    rel_spec_ports = {p for p in rel_spec_ports if (p.base_name in output_port_names)
                                                    or (p.is_input)}

    p_names = {p.unique_name for p in rel_spec_ports}

    rel_spec_ports = {port for port in list(spec_contract.ports_dict.values()) if port.unique_name in p_names}


    var_map, component_map = extract_model_connections(spec_contract, relevant_contracts,
                                                 output_port_names, library, manager)

    all_components = {type(comp): [] for comp in list(component_map.keys())}

    for c in list(component_map.keys()):
        all_components[type(c)].append(c)

    #composition names

    mapping = CompositionMapping(relevant_contracts | {w_spec})
    for c in relevant_contracts:
        for p in list(c.ports_dict.values()):
            mapping.add(p, '%s_%s' % (c.unique_name, p.base_name))

    #now build preamble and related formulas

    for c in relevant_contracts:
        c.assume_formula = Implication(Geq(component_map[c], Constant(0)), c.assume_formula)
        c.guarantee_formula = Implication(Geq(component_map[c], Constant(0)), c.guarantee_formula)

    if len(output_port_names) != len(spec_contract.output_ports_dict):
        composition = w_spec.compose(relevant_contracts, composition_mapping=mapping)
    else:
        root = relevant_contracts.pop()
        composition = root.compose(relevant_contracts, composition_mapping=mapping)
        relevant_contracts.add(root)

    #TODO: can we simplify this?
    ref_formulas = [build_formulas_for_other_spec(s, composition) for s in
                    list(spec_dict.values())]
    all_specs_formula = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), ref_formulas)
    
    neg_formula = build_neg_formula_for_all_specs(list(spec_dict.values()), composition)

    #process use components:
    #retrieve_component
    always_use = {spec_contract: {}}
    for inst, l in manager.fixed_components:
        c = all_components[type(inst.contract)][l]

        always_use[c] = {}

    # connections to spec
    for (inst, port_name, level, specport_name) in manager.fixed_connections_spec:
        c = all_components[type(inst.contract)][level]

        port = c.ports_dict[port_name]
        s_port = spec_contract.ports_dict[specport_name]

        if port.is_input and s_port.is_input:
            always_use[c][port] = s_port
        elif port.is_output and s_port.is_output and s_port.base_name in output_port_names:
            always_use[spec_contract][s_port] = port

    #connections among components
    for (comp1, port1_name, level1, comp2, port2_name, level2) in manager.fixed_connections:
        c1 = all_components[type(comp1.contract)][level1]
        c2 = all_components[type(comp2.contract)][level2]

        port1 = c1.ports_dict[port1_name]
        port2 = c2.ports_dict[port2_name]


        if port1.is_input and port2.is_output:
            always_use[c1][port1] = port2
        elif port1.is_output and port2.is_input:
            always_use[c2][port2] = port1

    formulas = []
    location_vars = {}
    loc_by_contract = {}
    location_map = {}
    inverse_location_vars = {}

    LOG.debug(component_map)

    # for c in list(component_map.values()):
    #     formulas.append(Geq(c, Constant(-1)))

    for port in var_map:
        p_map = []

        if port in port.contract.relevant_ports | rel_spec_ports:
            location_vars[port] = Literal('l', l_type=FrozenInt())
            location_map[location_vars[port]] = {}
            if port.contract not in loc_by_contract:
                loc_by_contract[port.contract] = set()
            loc_by_contract[port.contract].add(location_vars[port])
            count = 0
            #disconnected
            if port.contract in relevant_contracts and port.contract not in always_use:
                inner = Equivalence(location_vars[port], Constant(-1), merge_literals=False)
                inner = Conjunction(inner, Equivalence(component_map[port.contract], Constant(-1), merge_literals=False), merge_literals=False)

                p_map.append(inner)

            if port.contract in always_use and port in always_use[port.contract]:
                #remove all but the fix connection
                var_map[port] = {always_use[port.contract][port]}


            for p in var_map[port]:
                if p in p.contract.relevant_ports | rel_spec_ports:
                    if p.contract not in inverse_location_vars:
                        inverse_location_vars[p.contract] = {}
                    if p not in inverse_location_vars[p.contract]:
                        inverse_location_vars[p.contract][p] = {}

                    inverse_location_vars[p.contract][p][location_vars[port]] = count
                    inner = Equivalence(location_vars[port], Constant(count), merge_literals=False)

                    if port.contract in component_map: #does not include spec
                        inner = Conjunction(inner, Geq(component_map[port.contract], Constant(0), merge_literals=False), merge_literals=False)
                    location_map[location_vars[port]][count] = p
                    count += 1

                    inner2 = Globally(Equivalence(port.literal, p.literal, merge_literals=False))

                    if port.contract in relevant_contracts:
                        if p.contract in relevant_contracts:
                            #add level vars
                            lev_c = Lt(component_map[p.contract], component_map[port.contract], merge_literals=False) #no loops
                            
                            inner2 = Conjunction(inner2, lev_c, merge_literals=False)

                    else:
                        inner2 = Conjunction(inner2, Geq(component_map[p.contract], Constant(0)))

                    location_space = Conjunction(inner, inner2, merge_literals=False)
                    LOG.info(location_space)
                    p_map.append(location_space)

            if len(p_map) > 0:
                formula = reduce((lambda x, y: Disjunction(x, y, merge_literals=False)), p_map)
                formulas.append(formula)

    #we want to force a contract not connected to anything in output not to interfere
    all_cond = []
    for c in relevant_contracts:
        if c in inverse_location_vars:
            c_map = inverse_location_vars[c]
            port_fs = []

            for p, pairs in list(c_map.items()):
                inner_fs = []

                for loc, count in list(pairs.items()):
                    inner_fs.append(Negation(Equivalence(loc, Constant(count))))

                if len(inner_fs) > 0:
                    inner_fs = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), inner_fs)
                    port_fs.append(inner_fs)

            if len(port_fs) > 0:
                port_fs = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), port_fs)
                port_fs = Implication(Equivalence(component_map[c], Constant(-1)), port_fs)
                all_cond.append(port_fs)

    if len(all_cond) > 0:
        all_cond = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), all_cond)
    else:
        all_cond = TrueFormula()

    no_conn = []
    for c, lev in list(component_map.items()):
        if c in loc_by_contract:
            locs = loc_by_contract[c]

            l_cond = []
            for l in locs:
                l_cond.append(Equivalence(l, Constant(-1)))

            #set all ports to static
            for port in list(c.ports_dict.values()):
                if isinstance(port.l_type, Int):
                    l_cond.append(Globally(Equivalence(port.literal, Constant(0),
                                                       merge_literals=False)))
                elif isinstance(port.l_type, Bool):
                    l_cond.append(Globally(Equivalence(port.literal, FalseFormula(),
                                            merge_literals=False)))

            if len(l_cond) > 0:
                l_cond = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), l_cond)
                l_cond = Implication(Leq(lev, Constant(-1)), l_cond)
                no_conn.append(l_cond)

    if len(no_conn) > 0:
        no_conn = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), no_conn)
    else:
        no_conn = TrueFormula()

    guaranteed_if_used = TrueFormula()
    preamble = TrueFormula()

    if len(formulas) > 0:

        preamble = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), formulas)

        guaranteed_if_used = Conjunction(guaranteed_if_used, composition.guarantee_formula, merge_literals=False)
        specs_asmpt = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.assume_formula for s in list(spec_dict.values())])
        guaranteed_if_used = Conjunction(guaranteed_if_used, specs_asmpt, merge_literals=False)

    LOG.info(guaranteed_if_used)
    LOG.info(preamble)
    LOG.info(no_conn)
    LOG.info(all_cond)

    #TODO: This might need to come back
    # preamble = Conjunction(preamble, no_conn, merge_literals=False)
    preamble = Conjunction(preamble, all_cond, merge_literals=False)

    balance_f = build_balance_constraints(manager.synthesis_interface.balance_max_types, relevant_contracts,
                                          location_vars, location_map)
    if balance_f is not None:
        preamble = Conjunction(preamble, balance_f, merge_literals=False)

    # neg_check = Literal('n')

    # pos_left = Conjunction(preamble, composition.assume_formula, merge_literals=False)
    # pos_formula = Implication(pos_left, composition.guarantee_formula, merge_literals=False)

    # pos_check = Literal('p')
    # pos_formula = Implication(pos_formula, Globally(pos_check), merge_literals=False)


    # neg_ca_formula = Implication(preamble, Negation(composition.assume_formula), merge_literals=False)

    # neg_ca_check = Literal('a')
    # neg_ca_formula = DoubleImplication(neg_ca_formula, Globally(neg_ca_check), merge_literals=False)
    
    LOG.info(neg_formula)
    LOG.debug(all_specs_formula)
    # LOG.debug(pos_formula)
    LOG.debug(preamble)
    LOG.debug(guaranteed_if_used)

    # TODO process constants

    return (composition, spec_contract, rel_spec_ports, ref_formulas, all_specs_formula,
            neg_formula, preamble, guaranteed_if_used, var_map, component_map, location_vars,
            location_map, parameters)


def build_model_map(connected_spec, output_port_names,  manager, var_assign):
    '''
    Build a SMV model and checks if there is any possible alternative set of connections to satisfy the spec.
    We first need to create additional formulas to express flexible connections.
    :return:
    '''

    model_map = {}

    #now we need to collect all the components connected in chain to the spec output we are considering
    # we start with the model connected to the out
    spec_port_models = [manager.spec_out_dict[name] for name in output_port_names]

    for (orig_lev, orig_port) in var_assign:
        if orig_lev == -1:
            #that's the spec
            for mod in spec_port_models:
                name = str(mod)
                spec_port = connected_spec.ports_dict[name]

                if spec_port.base_name == orig_port.base_name:

                    #assert len(var_assign[(orig_lev, orig_port)]) == 1
                    c_level, c_port = var_assign[(orig_lev, orig_port)].pop()

                    model_map[mod.get_id()] = manager.lib_model.index[c_port][c_level]

        else:
            mod = manager.lib_model.model_by_port(orig_port)[orig_lev]

            c_level, c_port = var_assign[(orig_lev, orig_port)].pop()

            if c_level > -1:
                model_map[mod.get_id()] = manager.lib_model.index[c_port][c_level]

                # LOG.debug(manager.lib_model.index[c_level][c_port])
                # LOG.debug(manager.lib_model.port_by_index(manager.lib_model.index[c_level][c_port]).base_name)
            else:
                model_map[mod.get_id()] = manager.lib_model.spec_map[c_port.base_name]

    # LOG.debug(model_map)
    return model_map



def build_formulas_for_other_spec(spec_contract, composition):


    verifier = NuxmvRefinementStrategy(composition)
    ref_formula = verifier.get_refinement_formula(spec_contract)

    return ref_formula


def build_neg_formula_for_all_specs(spec_list, composition):

    spec_map = []

    specs_gnt = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.guarantee_formula for s in spec_list])

    g_check = specs_gnt
    a_check = composition.assume_formula

    return Negation(Conjunction(a_check, g_check, merge_literals=False))

# def _check_levels(in_p, out_p, lev_map, lev_vars):
#     '''
#     makes the nect function cleaner
#     :param in_p:
#     :param out_p:
#     :param lev_map:
#     :return:
#     '''

#     if lev_map is None:
#         return True

#     if not (out_p in lev_map and in_p in lev_map):
#         return True

#     if int(lev_vars[out_p.contract.unique_name]) < int(lev_vars[in_p.contract.unique_name]):
#         return True


#     return False

# def get_all_candidates(trace, var_map, relevant_allspecs_ports, lev_map=None, current_pool=None, conjoin=False):
#     ''' return a formula indicating all candidates from a trace'''
#     var_assign, lev_vars = trace_analysis(trace, var_map, lev_map)
#     #LOG.debug(var_assign)
#     v_assign = []

#     num = 1
#     candidate_connection = None
#     te_be_removed = set()

#     for p in var_assign:
#         p_opt = []

#         if current_pool is not None and p not in current_pool:
#             te_be_removed.add(p)
#             continue

#         if p not in p.contract.relevant_ports | relevant_allspecs_ports:
#             continue

#         num = num * len(var_assign[p])
#         inner_remove = set()
#         for v_p in var_assign[p]:
#             if current_pool is not None and v_p not in current_pool[p]:
#                 #remove
#                 # TODO: this is wrong, it doesn't have to divide now, but just remove one
#                 num = num / len(var_assign[p])
#                 inner_remove.add(v_p)
#                 continue
#             if not _check_levels(p, v_p, lev_map, lev_vars):
#                 continue

#             if v_p not in v_p.contract.relevant_ports | relevant_allspecs_ports:
#                 continue

#             p_opt.append(Globally(Equivalence(p.literal, v_p.literal, merge_literals=False)))

#         if len(p_opt) > 0:
#             if conjoin:
#                 temp = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), p_opt)
#             else:
#                 temp = reduce(lambda x, y: Disjunction(x, y, merge_literals=False), p_opt)
#             v_assign.append(temp)

#         for x in inner_remove:
#             var_assign[p].remove(x)
#     if len(v_assign) > 0:
#         candidate_connection = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), v_assign)

#     for x in te_be_removed:
#         var_assign.pop(x)

#     return candidate_connection, var_assign, num

# def pick_one_candidate(trace, var_map, relevant_allspecs_ports, manager, lev_map=None, current_pool=None):
#     ''' return a formula indicating all candidates from a trace'''
#     var_assign, lev_vars = trace_analysis(trace, var_map, lev_map)

#     v_assign = []
#     candidate_connection = None
#     new_var_assign = {}

#     for p in var_assign:

#         if p not in p.contract.relevant_ports | relevant_allspecs_ports:
#             continue

#         for v_p in var_assign[p]:

#             if not _check_levels(p, v_p, lev_map, lev_vars):
#                 continue

#             if v_p not in v_p.contract.relevant_ports | relevant_allspecs_ports:
#                 continue

#             v_assign.append(Globally(Equivalence(p.literal, v_p.literal, merge_literals=False)))
#             new_var_assign[p.unique_name] = v_p.unique_name
#             break

#     if len(v_assign) > 0:
#         candidate_connection = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), v_assign)

#     return candidate_connection, new_var_assign

def build_smv_module(module_formula, parameters, prefix=None, include_formula=TrueFormula()):
    '''
    returns a smv module string and its signature
    :param module_formula:
    :param parameters:
    :return:
    '''

    mod_vars = [x for (_, x) in module_formula.get_literal_items()]
    mod_vars = set(mod_vars) - set(parameters)
    aut = ltl2smv(include_formula, include_vars=mod_vars,
                  parameters=parameters, prefix=prefix)
    # LOG.debug(aut)

    autline = aut.split('\n', 1)[0]
    autsign = autline.split(' ', 1)[1]

    return autsign, aut

def build_smv_program(neg_autsign, neg_aut,
                      variables, neg_module_instances, spec_str, cex_modules='', cex_name_list=None):


    lvars_str = _process_var_decl(variables)

    if cex_name_list is None:
        cex_name_list = []

    for v in neg_module_instances:
        inst = 'VAR %s: %s;' % (v.unique_name, neg_autsign)
        lvars_str = lvars_str + '\n' + inst

    #create a one time use var
    for c, v in zip(cex_name_list, neg_module_instances):
        inst = 'VAR %s: %s(%s);' % (Literal('c').unique_name, c, v.unique_name)
        lvars_str = lvars_str + '\n' + inst

    base_module = MODULE_TEMPLATE % (lvars_str, spec_str)

    module = cex_modules + neg_aut + '\n' + base_module

    LOG.debug(module)

    return module

def exists_forall_learner(spec_contract, rel_spec_ports,
                          ref_formulas, all_specs_formula, neg_formula, 
                          preamble, guaranteed_if_used, var_map, component_map, input_variables,
                          location_vars, location_map, terminate_evt,
                          parameters, output_port_names, max_depth=None):
    """
    verify refinement formula according to preamble
    :param ref_formula:
    :param preamble:
    :param monitored_variables:
    :param checked_variables:
    :return:
    """

    l_passed = False
    spec_instance_dict = {Literal('m'): TrueFormula()}

    generated_cex = set()
    all_candidates = None
    inverse_location_vars = {y:x for (x,y) in list(location_vars.items())}
    do_cex_checks = True

    all_s_variables = set([p for p in list(spec_contract.ports_dict.values())])
    all_s_variables = all_s_variables & rel_spec_ports
    ntrace = trace = None
    param_list = [x for x in parameters]
    all_cex_modules = ''
    all_cex_names = set()

    total = 1
    for p in var_map:
        total *= len(var_map[p])

    current_pool = {}

    for port in var_map:
        current_pool[port] = set()

        for p in var_map[port]:
            current_pool[port].add(p)

    #LOG.debug("TOTAL: %d candidates" % total)

    if preamble is None:
        #no extra connections, we try directly if the composition works

        for ref_formula in ref_formulas:
            l_passed = verify_tautology(ref_formula, return_trace=False)

            if not l_passed:
                break
        LOG.debug("no preamble")
        LOG.debug(l_passed)
        return l_passed, None, None, None
    else:

        loc_limits = []
        for loc, lmap in list(location_map.items()):
            a = Geq(loc, Constant(-1))
            b = Leq(loc, Constant(len(lmap)-1))
            loc_limits.append(Conjunction(a, b, merge_literals=False))

        loc_c = None
        if len(loc_limits) > 0:
            loc_c = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), loc_limits)

        curr_depth = 0
        first_loop = True
        loop_counter = 0

        while first_loop or (max_depth is not None and curr_depth < max_depth):
            first_loop = False
            curr_depth += 1

            depth_constr = []
            depth_f = None
            # define max depth
            if max_depth is not None:
                for v in list(component_map.values()):
                    depth_constr.append(Lt(v, Constant(curr_depth)))

                depth_f = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), depth_constr)

            LOG.debug(preamble)
            LOG.debug(neg_formula)

            left = Conjunction(preamble, guaranteed_if_used, merge_literals=False)

            if max_depth is not None:
                left = Conjunction(depth_f, left, merge_literals=False)
                LOG.critical(f"SOLVING FOR DEPTH {curr_depth} for {output_port_names}")

            all_f = Implication(left, neg_formula, merge_literals=False)

            LOG.info(all_f)
            autsign, aut = build_smv_module(all_f, list(location_vars.values()) + list(component_map.values()) + param_list,
                                            prefix='0')

            while True:
                loop_counter += 1

                if terminate_evt.is_set():
                    return False, None, None, None

                checks_list = ['(%s)' % all_f.generate(symbol_set=NusmvSymbolSet,
                                                       prefix='%s.'%m.unique_name,
                                                      ignore_precedence=True)
                            for m in spec_instance_dict]

                checks_str = ' | '.join(checks_list)

                #negate solutions already tried
                if all_candidates is not None:
                    no_repeat = Negation(all_candidates)
                else:
                    no_repeat = TrueFormula()

                left = no_repeat
                # if loc_c is not None:
                #     left = Conjunction(loc_c, left, merge_literals=False)

                left = left.generate(symbol_set=NusmvSymbolSet, ignore_precedence=True)

                # Although in check_str we have renamed all the variables, including the location variables,
                # the fact that we are not renaming left will make sure that the location variables are the same
                # across all the smv modules. For instance, the formula (l_0 >= -1) -> (m_0.l_0 >= -2) is valid in
                # Nuxmv 1.1.1.
                # NB here we use a bunch of implications for deriving the synthesis constraint. It is actually equivalent
                # to what we report in the paper (negation of conjunctions) because here we negate the right-hand side
                base_spec_str = "(%s) -> (%s)" % (left, checks_str)

                LOG.info(left)
                LOG.info(checks_str)
                LOG.info(base_spec_str)

                smv = build_smv_program(autsign, aut, list(location_vars.values()) + list(component_map.values()) + param_list,
                                        list(spec_instance_dict.keys()), base_spec_str, all_cex_modules, all_cex_names)

                LOG.info(smv)
                
                l_passed, ntrace = verify_tautology_smv(smv, return_trace=True)
                LOG.info(ntrace)
                if l_passed:
                    # LOG.debug(smv)
                    # LOG.debug(cex)
                    # LOG.debug(ntrace)
                    # LOG.debug(trace)
                    # LOG.debug(neg_formula)
                    break
                # LOG.debug(ntrace)
                #analyze trace to derive possible solution
                all_locs = trace_analysis_for_loc(ntrace, list(location_vars.values()))
                uses = trace_analysis_for_loc(ntrace, list(component_map.values()))
                param_assign = trace_analysis_for_loc(ntrace, param_list)
                LOG.info(uses)
                LOG.info(all_locs)
                LOG.info(param_assign)

                locs, used_contracts = detect_reject_list(all_locs, location_vars, location_map,
                                          set(spec_contract.output_ports_dict.values()) & rel_spec_ports)
                LOG.info(locs)

                LOG.debug(location_map)

                #which components are really used?
                #remove spec from list
                used_contracts = used_contracts - {spec_contract}

                really_used = {component_map[c] for c in used_contracts}
                used_f = []
                for var, use in list(uses.items()):
                    if var in really_used:
                        used_f.append(Equivalence(var, Constant(use)))
                    else:
                        used_f.append(Equivalence(var, Constant(-1)))
                #done

                if len(used_f) > 0:
                    used_f = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), used_f)
                else:
                    used_f = TrueFormula()

                # now check if this is a good solution indeed
                constr = [TrueFormula()]
                lconstr = [TrueFormula()]
                for var, val in list(locs.items()):
                    lconstr.append(Equivalence(var, Constant(val), merge_literals=False))
                    if val >= 0:
                        # LOG.debug(location_map)
                        port = inverse_location_vars[var]
                        connected_p = location_map[var][val]
                        constr.append(Globally(Equivalence(port.literal, connected_p.literal, merge_literals=False)))

                # process parameters
                for p, v in list(param_assign.items()):
                    lconstr.append(Equivalence(p, Constant(v), merge_literals=False))
                    constr.append(Equivalence(p, Constant(v), merge_literals=False))
                #done

                conn = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), constr)
                lconn = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), lconstr)
                just_conn = conn
                LOG.info(used_f)
                LOG.info(just_conn)
                LOG.info(lconn)

                #new cex
                left = Conjunction(used_f, conn, merge_literals=False)
                LOG.info(left)
                # LOG.debug(conn)
                LOG.info(all_specs_formula)

                # print_model(locs, param_assign, inverse_location_vars, location_map, spec_contract, relevant_contracts, manager)

                passed, trace = verify_candidate(left, all_specs_formula)

                if not passed:
                    LOG.info(trace)
                    # LOG.debug(input_variables)
                    # get counterexample for inputs
                    cex, _ = derive_valuation_from_trace(trace, input_variables, max_horizon=NUXMV_BOUND*1.5)
                    # fullcex, _ = derive_valuation_from_trace(trace, all_s_variables, max_horizon=NUXMV_BOUND*1.5)

                    # LOG.debug(trace)
                    # LOG.debug(cex_mod)
                    LOG.info(cex)
                    # LOG.debug(fullcex)
                    #LOG.debug(full_in_cex)

                    # # PRINT
                    # n = 5
                    # if i >= n:
                    # #if l_passed:
                    # var_assign = {}
                    # for var, val in locs.items():
                    #     if val >= 0:
                    #         # LOG.debug(location_map)
                    #         port = inverse_location_vars[var]
                    #         connected_p = location_map[var][val]
                    #         var_assign[port.unique_name] = connected_p.unique_name
                    # LOG.debug(var_assign)
                    #
                    # composition, connected_spec, contract_inst = \
                    #     manager.build_composition_from_model(None, manager.spec_port_names,
                    #                                          relevant_contracts, var_assign)
                    #
                    # LOG.debug(connected_spec)
                    # from graphviz_converter import GraphizConverter
                    # graphviz_conv = GraphizConverter(connected_spec, composition, contract_inst,
                    #                                  filename='_'.join(manager.spec_port_names))
                    # graphviz_conv.generate_graphviz()
                    # graphviz_conv.view()
                    #
                    #     import time
                    #     time.sleep(10)
                    # if l_passed:
                    #     LOG.debug(smv)
                    #     return False, None, None
                    # #
                    # if i < n:
                    #     i += 1

                    #DONE: add check to make sure cex is agreeing with spec assumptions. 

                    if cex is not None:
                        cex_p = False
                        #check this is not a spurious cex
                        cex_check = Implication(cex, spec_contract.assume_formula, merge_literals=False)
                        valid = verify_tautology(cex_check, return_trace=False)

                        if valid:
                            for c in list(spec_instance_dict.values()):
                                cex_check = Implication(c, cex, merge_literals=False)
                                cex_p = verify_tautology(cex_check, return_trace=False)
                                if cex_p:
                                    LOG.debug('CEX already encoded')
                                    #assert False
                                    break
                            if not cex_p and do_cex_checks:
                                #if we have only the initial case, replace TRUE with the current CEX
                                if len(spec_instance_dict) == 1 and type(list(spec_instance_dict.values())[0]) is TrueFormula:
                                    spec_instance_dict[list(spec_instance_dict.keys())[0]] = cex
                                else:
                                    spec_instance_dict[Literal('m')] = cex
                                #spec_instance_dict[Literal('m')] = cex
                                generated_cex.add(cex)
                                LOG.debug(len(spec_instance_dict))
                                cex_name = Literal('cex_inst').unique_name
                                cex_mod = build_module_from_trace(trace, input_variables, cex_name)

                                LOG.info(cex_mod)
                                all_cex_modules += cex_mod
                                all_cex_names.add(cex_name)
                        else:
                            LOG.debug('Spurious CEX')
                            LOG.debug(cex)

                    LOG.info(lconn)
                    if all_candidates is None:
                        all_candidates = lconn
                    else:
                        all_candidates = Disjunction(all_candidates, lconn, merge_literals=False)
                    LOG.info(all_candidates)

                else:
                    left = Conjunction(used_f, just_conn, merge_literals=False)
                    passed, trace = verify_candidate(left, all_specs_formula)

                    # if not passed:
                    #     #do_cex_checks = False
                    #     LOG.debug('No CEXs')
                    #     if all_candidates is None:
                    #         all_candidates = lconn
                    #     else:
                    #         all_candidates = Disjunction(all_candidates, lconn, merge_literals=False)

                    #     continue

                    LOG.debug('FOUND')
                    print('')
                    print('loops until success:')
                    print(loop_counter)

                    var_assign = {}
                    for var, val in list(locs.items()):
                        if val >= 0:
                            # LOG.debug(location_map)
                            port = inverse_location_vars[var]
                            connected_p = location_map[var][val]
                            var_assign[port.unique_name] = connected_p.unique_name
                    LOG.debug(var_assign)
                    LOG.debug(param_assign)
                    return passed, conn, var_assign, param_assign

                LOG.critical('+++')

    return  False, None, None, None


def detect_reject_list(location_vals, location_vars, location_map, spec_vars):
    '''
    return a list of connections connected to the spec. ignore the spurious connections
    :param location_vals:
    :return:
    '''

    LOG.debug([p.base_name for p in spec_vars])

    port_list = set(spec_vars)
    seen = set()
    var_dict = {}
    used_contracts = set()

    while len(port_list) > 0:
        port = port_list.pop()

        if port not in seen and port in location_vars:
            seen.add(port)
            l = location_vars[port]
            val = location_vals[l]
            var_dict[l] = val

            if val == -1:
                continue
            else:
                other_p = location_map[l][val]
                contract = other_p.contract

                used_contracts.add(contract)

                for iport in list(contract.input_ports_dict.values()):
                    if iport not in var_dict:
                        port_list.add(iport)

    return (var_dict, used_contracts)

def verify_candidate(candidate, spec, no_loop=False):
    '''verify whether a candidate is a good one'''

    _candidate = Implication(candidate, spec, merge_literals=False)

    if no_loop:
        source = NuxmvPathLoader.get_source_path_noloop()
    else:
        source = NuxmvPathLoader.get_source_path()

    l_passed, trace = verify_tautology(_candidate,
                                       source_location=source,
                                       return_trace=True)

    return l_passed, trace


# def assemble_checked_vars(trace_diff, monitored_vars, checked_vars):
#     """
#     Take the trace diff from trace_analysis and updates the checked_vars dict
#     :param trace_diff:
#     :param connected_contracts:
#     :param checked_vars:
#     :return:
#     """

#     # LOG.debug(checked_vars)
#     for p in monitored_vars:

#         lev, orig_p = monitored_vars[p]['orig']

#         for v_p in trace_diff[p]:
#             _, old_v_p = monitored_vars[p]['ports'][v_p]
#             checked_vars[(lev, orig_p)].add(old_v_p.base_name)

#     # LOG.debug(checked_vars)
#     return checked_vars


def print_model(locs, param_assign, inverse_location_vars, location_map, spec_contract, relevant_contracts, manager):
    '''
    calls graphviz and generate a graphical representation of the model
    :return:
    '''

    var_assign = {}
    for var, val in list(locs.items()):
        if val >= 0:
            # LOG.debug(location_map)
            port = inverse_location_vars[var]
            connected_p = location_map[var][val]
            var_assign[port.unique_name] = connected_p.unique_name
    LOG.debug(var_assign)

    param_assign = {x.unique_name: v for x, v in list(param_assign.items())}

    # convert names in spec to original spec
    for name, port in list(spec_contract.ports_dict.items()):
        uname = port.unique_name
        orig_port = manager.spec.ports_dict[name]

        if uname in var_assign:
            var_assign[orig_port.base_name] = var_assign[uname]
            var_assign.pop(uname)
        else:
            for name in var_assign:
                if uname == var_assign[name]:
                    var_assign[name] = orig_port.base_name

    composition, connected_spec, contract_inst, param_assign = \
        manager.build_composition_from_model(None, manager.spec_port_names,
                                             relevant_contracts, var_assign, params=param_assign, build_copy=True)

    LOG.debug(connected_spec)
    from .graphviz_converter import GraphizConverter
    graphviz_conv = GraphizConverter(connected_spec, composition, contract_inst,
                                     parameters_values=param_assign,
                                     filename='_'.join(manager.spec_port_names))
    graphviz_conv.generate_graphviz()
    graphviz_conv.view()