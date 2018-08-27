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
from pycolite.types import FrozenInt, Int, FrozenBool, FrozenVar
from pycolite.nuxmv import (NuxmvRefinementStrategy, verify_tautology, verify_tautology_smv,
                            ltl2smv, _process_var_decl, MODULE_TEMPLATE, derive_valuation_from_trace,
                            trace_analysis_for_loc, build_module_from_trace)
from pycolite.parser.parser import LTL_PARSER
from pycolite.util.util import NUXMV_BOUND
from multiprocessing import *


def parallel_solve(spec_list, output_port_names, model, manager, pid, found_evt, found_queue, terminate_evt):
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
    checked_variables = None

    first = True
    spec_map = None
    first_spec = None
    composition = None
    var_assign = {}

    rel_spec_ports = set()
    for spec in spec_list:
        rel_spec_ports |= spec.relevant_ports

    (contracts, composition, connected_spec,
     ref_formula, preamble, monitored, _) = process_model(manager.spec_contract, output_port_names, rel_spec_ports,
                                                   model, manager)


    to_remove = []
    for c in monitored:
        if len(monitored[c]['ports']) == 0:
            to_remove.append(c)

    for c in to_remove:
        del monitored[c]

    model_map = {}
    processes = []
    if len(monitored) == 0:
        # LOG.debug('here')
        proc = ParallelSolver(model, manager.spec_contract, None, None, None, None,
                              monitored, manager, model_map,
                              pid, found_evt, found_queue, terminate_evt)

        proc.start()

        processes.append(proc)

    else:
        (port, inner_d) = monitored.popitem()

        (level, orig_p) = inner_d['orig']

        # connections = inner_d['ports'].keys()

        for c in inner_d['ports']:
            c_lev, c_orig = inner_d['ports'][c]

            proc = ParallelSolver(model, manager.spec_contract, level, orig_p, c_lev, c_orig,
                                  monitored, manager, model_map,
                                  pid, found_evt, found_queue, terminate_evt)

            proc.start()

            processes.append(proc)

    for p in processes:
        p.join()

    if not found_evt.is_set():
        return False

    return True


class ParallelSolver(Process):
    """
    solves a single variable assignment
    """

    def __init__(self, model, spec, lev1, port1, lev2, port2, monitored, manager, model_map,
                 init_pid, found_evt, found_queue, terminate_evt):
        """
        constructor
        """
        # self.contracts = contracts
        self.model = model
        self.spec = spec
        self.monitored = monitored
        self.port1 = port1
        self.lev1 = lev1
        self.lev2 = lev2
        self.port2 = port2
        self.manager = manager
        self.model_map = model_map
        self.init_pid = init_pid
        self.terminate_evt = terminate_evt
        self.found_evt = found_evt
        self.found_queue = found_queue


        super(ParallelSolver, self).__init__()



    def check_all_specs_threadsafe(self, model):
        '''
        check if the model satisfies a number of specs, if provided
        '''

        composition = None
        connected_spec = None
        contract_inst = None
        failed_spec = None
        for spec in self.manager.specification_list:

            if self.terminate_evt.is_set():
                return False, None, None, None, None

            # with z3_lock:
            composition, connected_spec, contract_inst = \
                    self.manager.build_composition_from_model(model, spec, self.manager.spec_port_names,
                                                              model_index_map=self.model_map)

            if not composition.is_refinement(connected_spec):
                if self.ident % 20 == 0:
                    print('.'),
                failed_spec = spec
                # LOG.debug(failed_spec.guarantee_formula.generate())
                return False, composition, connected_spec,contract_inst, failed_spec

            print('+'),

        print('#'),
        return True, composition, connected_spec,contract_inst, None


    def __update_map(self, orig_lev1, orig_port1, orig_lev2, orig_port2):
        """
        update model maps
        :return:
        """

        spec_port_models = [self.manager.spec_out_dict[name] for name in self.manager.spec_port_names]

        if orig_lev1 == -1:
            #that's the spec
            for mod in spec_port_models:
                name = str(mod)
                spec_port = self.spec.ports_dict[name]

                if spec_port.base_name == orig_port1.base_name:
                    self.model_map[mod.get_id()] = self.manager.lib_model.index[orig_port2][orig_lev2]

        else:
            mod = self.manager.lib_model.model_by_port(orig_port1)[orig_lev1]


            if orig_lev2 > -1:
                self.model_map[mod.get_id()] = self.manager.lib_model.index[orig_port2][orig_lev2]

                # LOG.debug(manager.lib_model.index[c_level][c_port])
                # LOG.debug(manager.lib_model.port_by_index(manager.lib_model.index[c_level][c_port]).base_name)
            else:
                self.model_map[mod.get_id()] = self.manager.lib_model.spec_map[orig_port2.base_name]

        return



    def run(self):
        """
        takes its own options and run several solvers
        :return:
        """

        processes = []

        # LOG.debug('start')
        if self.terminate_evt.is_set():
            return

        # update map
        if self.lev1 is not None:
            self.__update_map(self.lev1, self.port1, self.lev2, self.port2)

        if len(self.monitored) == 0:

            # LOG.debug('checking')
            #ok, solve now
            state, composition, connected_spec, contract_inst, failed_spec = \
                self.check_all_specs_threadsafe(self.model)

            # LOG.debug(state)
            if state:

                # LOG.debug('done')
                self.found_queue.put((self.init_pid, frozenset(self.model_map.items())))
                self.found_evt.set()

            return

        else:

            # LOG.debug('recursion top')
            (port, inner_d) = self.monitored.popitem()

            (level, orig_p) = inner_d['orig']

            # connections = inner_d['ports'].keys()

            for c in inner_d['ports']:

                c_lev, c_orig = inner_d['ports'][c]

                # LOG.debug('recursion')
                proc = ParallelSolver(self.model, self.spec, level, orig_p, c_lev, c_orig,
                                      self.monitored, self.manager, self.model_map,
                                      self.init_pid, self.found_evt, self.found_queue, self.terminate_evt)

                proc.start()

                processes.append(proc)

            for p in processes:
                p.join()

        return




def counterexample_analysis(spec_list, output_port_names, model, relevant_contracts, manager, pid,
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
    checked_variables = None

    first = True
    spec_map = None
    first_spec = None
    composition = None
    var_assign = {}
    original_spec = manager.spec

    print('*'),
    #spec_list[0] = original_spec.copy()
    # (contracts, composition, connected_spec,
    #  ref_formula, preamble, monitored, model_map) = process_model(spec, output_port_names, rel_spec_ports,
    #                                                               model, manager)
    #
    # return False, composition, connected_spec, contracts, model_map
    if terminate_evt.is_set():
        return False, composition, connected_spec, contracts, model_map

    (composition, spec_contract, rel_spec_ports,
     ref_formulas, all_specs_formula, pos_formula, pos_check,
     neg_ca_formula, neg_ca_check, neg_formula,
     neg_check, preamble, left_sides,
     var_map, lev_map, location_vars, location_map,
     parameters) = process_model(spec_list, output_port_names,
                                                     model, relevant_contracts, manager)

    input_variables = set([p for p in spec_contract.input_ports_dict.values()])
    input_variables = input_variables & rel_spec_ports


        # from graphviz_converter import GraphizConverter
        # graphviz_conv = GraphizConverter(connected_spec, composition, contracts)
        # graphviz_conv.generate_graphviz()
        # graphviz_conv.view()

    # else:
    #     #other specs have different unique names
    #     # LOG.debug('here')
    #     ref_formula = build_formulas_for_other_spec(connected_spec, spec, composition)


    #performs first step of learning loo?p
    passed, candidate, var_assign, param_assign = exists_forall_learner(composition, spec_contract, rel_spec_ports,
                                                          ref_formulas, all_specs_formula,
                                                          neg_formula, neg_check, pos_formula, pos_check,
                                                          neg_ca_formula, neg_ca_check,
                                                          preamble, left_sides,
                                                        var_map, lev_map, input_variables,
                                                          location_vars, location_map,
                                                          terminate_evt, manager,
                                                        relevant_contracts, parameters,
                                                            max_depth=manager.max_depth)
    # LOG.debug(passed)
    # while not passed:
    #     #check again if terminate is set
    #     if terminate_evt.is_set():
    #         return False, composition, connected_spec, contracts, model_map
    #
    if not passed:
        #nope, not found
        LOG.debug('nope')
        # assert False
        return False, composition, connected_spec, contracts, model_map

        # else:

            # LOG.debug(candidate.generate())

            # passed, candidate, new_preamble, var_assign = exists_forall_learner(ref_formula, new_preamble, monitored, input_variables)


    # convert names in spec to original spec
    for name, port in spec_contract.ports_dict.items():
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
    param_assign = {x.unique_name: v for x, v in param_assign.items()}

    # preamble = new_preamble
    # LOG.debug('spec done')
    LOG.debug(model)
    LOG.debug(var_assign)
    LOG.debug(candidate)
    LOG.debug(param_assign)

    #if we are here we passed
    #we need to build model map
    # LOG.debug('found')

    # model_map = build_model_map(connected_spec, output_port_names,  manager, var_assign)

    # checked_vars = assemble_checked_vars(var_assign, monitored, checked_variables)
    # 
    # (contracts, composition, connected_spec,
    # ref_formula, preamble, monitored,
    # checked_variables, model_map) = process_model(first_spec, output_port_names, rel_spec_ports,
    #                                            model, manager, checked_variables=checked_vars)


    # LOG.debug(model_map)
    # LOG.debug(candidate.generate())
    # from graphviz_converter import GraphizConverter
    # graphviz_conv = GraphizConverter(connected_spec, composition, contracts)
    # graphviz_conv.generate_graphviz()
    # graphviz_conv.view()

    # assert False
    # here only if all are true


    if passed:
        LOG.debug('done')
        result_queue.put((pid, frozenset(var_assign.items()), frozenset(param_assign.items())))
        found_event.set()
        terminate_evt.set()

    return passed


def extract_model_connections(spec_contract, relevant_contracts, output_port_names, library):
    '''
    Extract possible connections form model
    :return:
    '''

    #build dict with ports and possible connections

    var_map = {}

    #create contract level variables(use contract names)
    lev_map = {}

    #let's start with the spec
    for name in output_port_names:
        s_port = spec_contract.ports_dict[name]
        var_map[s_port] = set()
        #only output for spec
        # lev_map[s_port] = Literal(s_port.contract.unique_name, l_type=FrozenInt())

        for c in relevant_contracts:
            for oport in c.output_ports_dict.values():

                if library.check_connectivity(s_port, oport):
                    var_map[s_port].add(oport)


    #now inter contract connections
    for ci in relevant_contracts:
        lev_map[ci] = Literal(ci.unique_name, l_type=FrozenInt())
        for iport in ci.input_ports_dict.values():
            var_map[iport] = set()

            for co in relevant_contracts - {ci}:
                for oport in co.output_ports_dict.values():

                    if library.check_connectivity(iport, oport):
                        var_map[iport].add(oport)


            #and input specs
            for s_port in spec_contract.input_ports_dict.values():
                if library.check_connectivity(iport, s_port):
                    var_map[iport].add(s_port)

        # #only for levels
        # for oport in ci.output_ports_dict.values():
        #     lev_map[oport] = Literal(oport.contract.unique_name, l_type=FrozenInt())

    # #merge all the lev vars for ports in the same contract
    # l = lev_map.values()
    # for v in l:
    #     for v1 in l:
    #         if v.base_name == v1.base_name:
    #             v.merge(v1)

    #LOG.debug(var_map)
    return var_map, lev_map


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
            for op in c.output_ports_dict.values():
                if c.port_type[op.base_name] == out_t:
                    temp_op = op
                if c.port_type[op.base_name] == outqt_t:
                    temp_oq = op

            if temp_op is not None and temp_oq is not None:
                temp_map[(temp_op, temp_oq)] = set()

        for c in contracts:
            temp_ip = None
            temp_qnt = None

            for ip in c.input_ports_dict.values():
                if c.port_type[ip.base_name] == in_t:
                    temp_ip = ip
                    break

            for op in c.output_ports_dict.values():
                if c.port_type[op.base_name] == inqt_t:
                    temp_qnt = op
                    break


            if temp_ip is not None and temp_qnt is not None:
                for k in temp_map:
                    temp_map[k].add((temp_ip, temp_qnt))

                map_balance.update(temp_map)


    #second phase, build formula
    all_c = []
    for (op, oq), setp in map_balance.items():
        in_constr = []
        vlist = []
        for ip, iq in setp:
            if ip in location_vars:
                vq = Literal('q', l_type=FrozenInt())
                il = location_vars[ip]
                lval = [k for k,v in location_map[il].items() if v == op]
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

    return all_f



def process_model(spec_list, output_port_names,
                  model, relevant_contracts, manager):
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
    parameters = {x.literal for c in relevant_contracts for x in c.output_ports_dict.values() if isinstance(x.l_type, FrozenVar) and x in c.relevant_ports}

    partial_spec = False
    if len(output_port_names) != len(spec_contract.output_ports_dict):
        partial_spec = True

    # composition mapping to define new names
    # mapping = CompositionMapping(contracts| set([working_spec]))

    parameters_by_contract = {}
    for c in relevant_contracts:
        p_set = set()

        for port in c.output_ports_dict.values():
            if port.literal in parameters:
                p_set.add(port.literal)

        parameters_by_contract[c] = p_set


    #uniform specs
    for ws in spec_dict.values():
        for port in ws.ports_dict.values():
            name = port.base_name

            spec_contract.connect_to_port(spec_contract.ports_dict[name], port)

    #if partial_spec:
    # process working spec
    for ws in working_specs.values():
        for port in ws.ports_dict.values():
            name = port.base_name

            if name not in output_port_names:
                spec_contract.connect_to_port(spec_contract.ports_dict[name], port)


    #build single contract for working specs
    all_guarantees = reduce(lambda x,y: Conjunction(x, y, merge_literals=False),
                            [ws.guarantee_formula for ws in working_specs.values()])
    all_assumptions = reduce(lambda x,y: Conjunction(x, y, merge_literals=False),
                             [ws.assume_formula for ws in working_specs.values()])

    w_spec = working_specs.values()[0]
    w_spec.assume_formula = all_assumptions
    w_spec.guarantee_formula = all_guarantees


    #extend with fixed components
    for spec in spec_dict.values():
        for c in manager.retrieve_fixed_components():
            spec.assume_formula = Conjunction(spec.assume_formula, c.assume_formula, merge_literals=False)


    rel_spec_ports = set()
    for spec in spec_dict.values():
        rel_spec_ports |= spec.relevant_ports


    rel_spec_ports = {p for p in rel_spec_ports if (p.base_name in output_port_names)
                                                    or (p.is_input)}

    p_names = {p.unique_name for p in rel_spec_ports}

    rel_spec_ports = {port for port in spec_contract.ports_dict.values() if port.unique_name in p_names}


    var_map, component_map = extract_model_connections(spec_contract, relevant_contracts,
                                                 output_port_names, library)



    #composition names
    #mappings = {s.unique_name: CompositionMapping(relevant_contracts | {working_specs[s.unique_name]}) for s in spec_list}

    mapping = CompositionMapping(relevant_contracts | {w_spec})
    for c in relevant_contracts:
        for p in c.ports_dict.values():
            mapping.add(p, '%s_%s' % (c.unique_name, p.base_name))

    #now build preamble and related formulas
    # compositions = {s.unique_name: working_specs[s.unique_name].compose(relevant_contracts, composition_mapping=mappings[s.unique_name])
    #                 for s in spec_list}

    # #make compositions port names uniform
    # for c1 in compositions.values():
    #     for c2 in compositions.values():
    #         for p_name in c1.ports_dict:
    #             c1.connect_to_port(c1.ports_dict[p_name], c2.ports_dict[p_name])


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
                    spec_dict.values()]
    all_specs_formula = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), ref_formulas)
    # temp = all_specs_formula.get_literal_items()
    # temp = {literal.unique_name for _, literal in temp}
    # relevant_allspecs_ports = {port for port in spec_contract.ports_dict.values() if port.unique_name in temp}


    # ref_formula = build_formula_for_all_specs(spec_contract, spec_list, composition)
    neg_formula = build_neg_formula_for_all_specs(spec_dict.values(), composition)

    # neg_formula = Negation(reduce(lambda x, y: Conjunction(x, y, merge_literals=False), ref_formulas))

    formulas = []
    location_vars = {}
    loc_by_contract = {}
    location_map = {}
    inverse_location_vars = {}

    LOG.debug(component_map)
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
            # #location_map[location_vars[port]][-1] = None
            if port.contract in relevant_contracts:
                inner = Leq(location_vars[port], Constant(-1), merge_literals=False)
                inner = Conjunction(inner, Equivalence(component_map[port.contract], Constant(-1), merge_literals=False), merge_literals=False)
                # #inner = Implication(inner, TrueFormula(), merge_literals=False)
                p_map.append(inner)
            for p in var_map[port]:
                if p in p.contract.relevant_ports | rel_spec_ports:
                    if p.contract not in inverse_location_vars:
                        inverse_location_vars[p.contract] = {}
                    if p not in inverse_location_vars[p.contract]:
                        inverse_location_vars[p.contract][p] = set()

                    inverse_location_vars[p.contract][p].add((count, location_vars[port]))
                    inner = Equivalence(location_vars[port], Constant(count), merge_literals=False)

                    if port.contract in component_map: #does not include spec
                        inner = Conjunction(inner, Geq(component_map[port.contract], Constant(0), merge_literals=False), merge_literals=False)
                    location_map[location_vars[port]][count] = p
                    count += 1

                    inner2 = Globally(Equivalence(port.literal, p.literal, merge_literals=False))

                    if port.contract in relevant_contracts:
                        if p.contract in relevant_contracts:
                            #add level vars
                            lev_c = Lt(component_map[p.contract], component_map[port.contract]) #no loops
                            # lev_c = Geq(component_map[p.contract], Constant(0)) #yes loops
                            #lev_c = Conjunction(lev_c, min_c, merge_literals=False)
                        # else:
                        #     #it's the spec
                        #     lev_c = Geq(component_map[port.contract], Constant(0))

                            inner2 = Conjunction(inner2, lev_c, merge_literals=False)

                    else:
                        inner2 = Conjunction(inner2, Geq(component_map[p.contract], Constant(0)))

                    inner = Conjunction(inner, inner2, merge_literals=False)

                    p_map.append(inner)

            if len(p_map) > 0:
                formula = reduce((lambda x, y: Disjunction(x, y, merge_literals=False)), p_map)
                formulas.append(formula)


    #we want to force a contract not connected to anything in output not to interfere
    all_cond = []
    for c in relevant_contracts:
        if c in inverse_location_vars:
            c_map = inverse_location_vars[c]
            port_fs = []

            for p, pairs in c_map.items():
                inner_fs = []

                for count, loc in pairs:
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
    for c, lev in component_map.items():
        if c in loc_by_contract:
            locs = loc_by_contract[c]

            l_cond = []
            for l in locs:
                l_cond.append(Equivalence(l, Constant(-1)))

            if len(l_cond) > 0:
                l_cond = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), l_cond)
                l_cond = Implication(Equivalence(lev, Constant(-1)), l_cond)
                no_conn.append(l_cond)


    if len(no_conn) > 0:
        no_conn = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), no_conn)
    else:
        no_conn = TrueFormula()



    #process parameter constraints
    params_constr = []
    for c, lev in component_map.items():
        if c in parameters_by_contract:
            p_set = parameters_by_contract[c]

            p_cond = []
            for p in p_set:
                p_cond.append(Equivalence(p, Constant(-1)))

            if len(p_cond) > 0:
                p_cond = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), p_cond)
                p_cond = Implication(Equivalence(lev, Constant(-1)), p_cond)
                params_constr.append(p_cond)
    if len(params_constr) > 0:
        params_f = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), params_constr)
    else:
        params_f = TrueFormula()

    # #process distinct ports
    # for p1, p2, in manager.library.distinct_ports_set:
    #     temp = process_distinct_lib_ports(p1, p2, var_map)
    #     formulas.append(temp)

    # #process distinct specs
    # for p1, p2, in manager.z3_interface.distinct_spec_port_set:
    #     temp = process_distinct_spec_ports(p1, p2, spec_contract, var_map)
    #     formulas.append(temp)

    left_sides = TrueFormula()
    preamble = TrueFormula()

    if len(formulas) > 0:

        preamble = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), formulas)


        left_sides = Conjunction(left_sides, composition.guarantee_formula, merge_literals=False)

        for s in spec_dict.values():
            left_sides = Conjunction(left_sides, s.assume_formula, merge_literals=False)
            #break


    encoded_connections = preamble
    no_conn = Conjunction(no_conn, all_cond, merge_literals=False)
    preamble = Conjunction(preamble, no_conn, merge_literals=False)
    preamble = Conjunction(preamble, params_f, merge_literals=False)



    # #all siblings together
    # c_conds = [TrueFormula()]
    # for contract in relevant_contracts:
    #     all_c = manager.library.contract_with_siblings(contract)
    #     eqs_neg = [TrueFormula()]
    #     eqs_pos = [TrueFormula()]
    #     for c in all_c & relevant_contracts:
    #         eqs_neg.append(Equivalence(component_map[c], Constant(-1), merge_literals=False))
    #         eqs_pos.append(Geq(component_map[c], Constant(0), merge_literals=False))
    #
    #     eqs_neg = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), eqs_neg)
    #     eqs_pos = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), eqs_pos)
    #
    #     c_conds.append(Implication(Equivalence(component_map[contract], Constant(-1), merge_literals=False), eqs_neg))
    #     c_conds.append(Implication(Geq(component_map[contract], Constant(0), merge_literals=False), eqs_pos))
    #
    #
    # c_conds = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), c_conds)
    # preamble = Conjunction(preamble, c_conds, merge_literals=False)

    balance_f = build_balance_constraints(manager.z3_interface.balance_max_types, relevant_contracts,
                                          location_vars, location_map)
    if balance_f is not None:
        preamble = Conjunction(preamble, balance_f, merge_literals=False)


    #add constraints for fixed components:
    fix = []
    for c in manager.retrieve_fixed_components():
        fix.append(Geq(component_map[c], Constant(0), merge_literals=False))

    if len(fix) > 0:
        fix = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), fix)
        preamble = Conjunction(preamble, fix, merge_literals=False)


    left = Conjunction(preamble, left_sides, merge_literals=False)
    autf = Implication(left, neg_formula, merge_literals=False)

    neg_check = Literal('n')

    #neg_formula = Implication(autf, Globally(neg_check), merge_literals=False)

    pos_left = Conjunction(preamble, composition.assume_formula, merge_literals=False)
    pos_formula = Implication(pos_left, composition.guarantee_formula, merge_literals=False)

    pos_check = Literal('p')
    pos_formula = Implication(pos_formula, Globally(pos_check), merge_literals=False)


    neg_ca_formula = Implication(preamble, Negation(composition.assume_formula), merge_literals=False)

    neg_ca_check = Literal('a')
    neg_ca_formula = DoubleImplication(neg_ca_formula, Globally(neg_ca_check), merge_literals=False)
    # #additional bit
    # add_bit = Conjunction(preamble, all_specs_formula, merge_literals=False)
    # add_bit = Implication(Negation(Globally(neg_check)), add_bit, merge_literals=False)
    #
    # neg_formula = Conjunction(neg_formula, add_bit, merge_literals=False)

    LOG.debug(neg_formula)
    LOG.debug(all_specs_formula)
    LOG.debug(pos_formula)

    # passed, trace = verify_tautology(Negation(preamble), return_trace=True)
    # LOG.debug(trace)
    # LOG.debug(preamble)
    #LOG.debug(location_map)
    # #name map
    # var_name_map = {}
    # for c in [spec_contract] + relevant_contracts:
    #     for p in c.ports_dict.values():
    #         var_name_map[p.unique_name] = p

    # TODO process constants

    return (composition, spec_contract, rel_spec_ports, ref_formulas, all_specs_formula, pos_formula, pos_check,
            neg_ca_formula, neg_ca_check, neg_formula, neg_check, preamble, left_sides, var_map, component_map, location_vars,
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

            #assert len(var_assign[(orig_lev, orig_port)]) == 1
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

    #specs_asm = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.assume_formula for s in spec_list])
    specs_gnt = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.guarantee_formula for s in spec_list])

    g_check = specs_gnt
    # a_check = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [compositions[s.unique_name].assume_formula for s in spec_list])
    a_check = composition.assume_formula

    return Negation(Conjunction(a_check, g_check, merge_literals=False))
    # neg_ref = Negation(ref_formula)

# def build_formula_for_all_specs(connected_spec, spec_list, composition):
#
#     spec_map = []
#
#     for spec_contract in spec_list:
#         for p_name in connected_spec.ports_dict:
#             # spec_map.append(Equivalence(spec_contract.ports_dict[p_name].literal, connected_spec.ports_dict[p_name].literal, merge_literals=False))
#
#             connected_spec.connect_to_port(connected_spec.ports_dict[p_name], spec_contract.ports_dict[p_name])
#
#     #specs_asm = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.assume_formula for s in spec_list])
#     specs_gnt = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.guarantee_formula for s in spec_list])
#
#     g_check = Implication(composition.guarantee_formula, specs_gnt, merge_literals=False)
#     a_check = Implication(spec_list[0].assume_formula, composition.assume_formula, merge_literals=False)
#
#
#     return Conjunction(a_check, g_check, merge_literals=False)


def _check_levels(in_p, out_p, lev_map, lev_vars):
    '''
    makes the nect function cleaner
    :param in_p:
    :param out_p:
    :param lev_map:
    :return:
    '''

    if lev_map is None:
        return True

    if not (out_p in lev_map and in_p in lev_map):
        return True

    if int(lev_vars[out_p.contract.unique_name]) < int(lev_vars[in_p.contract.unique_name]):
        return True


    return False

def get_all_candidates(trace, var_map, relevant_allspecs_ports, lev_map=None, current_pool=None, conjoin=False):
    ''' return a formula indicating all candidates from a trace'''
    var_assign, lev_vars = trace_analysis(trace, var_map, lev_map)
    #LOG.debug(var_assign)
    v_assign = []

    num = 1
    candidate_connection = None
    te_be_removed = set()

    for p in var_assign:
        p_opt = []

        if current_pool is not None and p not in current_pool:
            te_be_removed.add(p)
            continue

        if p not in p.contract.relevant_ports | relevant_allspecs_ports:
            continue

        num = num * len(var_assign[p])
        inner_remove = set()
        for v_p in var_assign[p]:
            if current_pool is not None and v_p not in current_pool[p]:
                #remove
                # TODO: this is wrong, it doesn't have to divide now, but just remove one
                num = num / len(var_assign[p])
                inner_remove.add(v_p)
                #var_assign[p].remove(v_p)
                continue
            if not _check_levels(p, v_p, lev_map, lev_vars):
                continue

            if v_p not in v_p.contract.relevant_ports | relevant_allspecs_ports:
                continue

            p_opt.append(Globally(Equivalence(p.literal, v_p.literal, merge_literals=False)))

        if len(p_opt) > 0:
            if conjoin:
                temp = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), p_opt)
            else:
                temp = reduce(lambda x, y: Disjunction(x, y, merge_literals=False), p_opt)
            v_assign.append(temp)

        for x in inner_remove:
            var_assign[p].remove(x)
    if len(v_assign) > 0:
        candidate_connection = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), v_assign)

    for x in te_be_removed:
        var_assign.pop(x)

    return candidate_connection, var_assign, num

def pick_one_candidate(trace, var_map, relevant_allspecs_ports, manager, lev_map=None, current_pool=None):
    ''' return a formula indicating all candidates from a trace'''
    var_assign, lev_vars = trace_analysis(trace, var_map, lev_map)

    v_assign = []
    candidate_connection = None
    new_var_assign = {}

    # #preprocess for distinct set
    # #TODO: this loop might be buggy. what if several constraints are set at once
    # for (p1, p2) in manager.library.distinct_ports_set:
    #     if p1 in var_assign and p2 in var_assign:
    #
    #         if len(var_assign[p1]) == 1:
    #             var_assign[p2] = var_assign[p2] - var_assign[p1]
    #         elif len(var_assign[p2]) == 1:
    #             var_assign[p1] = var_assign[p1] - var_assign[p2]
    #         else:
    #             var_assign[p1] = {var_assign[p1].pop()}
    #             var_assign[p2] = var_assign[p2] - var_assign[p1]

    for p in var_assign:
        p_opt = []

        # LOG.debug('1')
        if p not in p.contract.relevant_ports | relevant_allspecs_ports:
            continue
        # LOG.debug('2')
        #new_var_assign[p] = set()
        for v_p in var_assign[p]:

            # LOG.debug('1.1')
            if not _check_levels(p, v_p, lev_map, lev_vars):
                continue

            # LOG.debug('1.2')

            if v_p not in v_p.contract.relevant_ports | relevant_allspecs_ports:
                continue


            # LOG.debug('1.3')
            v_assign.append(Globally(Equivalence(p.literal, v_p.literal, merge_literals=False)))
            new_var_assign[p.unique_name] = v_p.unique_name
            break


    if len(v_assign) > 0:
        candidate_connection = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), v_assign)


    return candidate_connection, new_var_assign

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
        #inst = 'JUSTICE %s.%s;' % (v.unique_name, check_var.unique_name)
        #lvars_str = lvars_str + '\n' + inst


    #create a one time use var
    for c, v in zip(cex_name_list, neg_module_instances):
        inst = 'VAR %s: %s(%s);' % (Literal('c').unique_name, c, v.unique_name)
        lvars_str = lvars_str + '\n' + inst

    # for v in pos_module_instances:
    #     inst = 'VAR %s: %s;' % (v.unique_name, pos_autsign)
    #     lvars_str = lvars_str + '\n' + inst
    #
    #
    # for v in neg_ca_module_instances:
    #     inst = 'VAR %s: %s;' % (v.unique_name, neg_ca_autsign)
    #     lvars_str = lvars_str + '\n' + inst


    #check formula
    #spec_str = spec_formula.generate(symbol_set=NusmvSymbolSet,
    #                               ignore_precedence=True)

    base_module = MODULE_TEMPLATE % (lvars_str, spec_str)

    module = cex_modules + neg_aut + '\n' + base_module

    #module = pos_aut + '\n' + module

    #module = neg_ca_aut + '\n' + module

    LOG.debug(module)

    return module


def reject_all_equivalent(locs, relevant_contracts, location_vars):
    '''
    reject equivalent configurations.
    :param locs:
    :param relevant_contracts:
    :param location_vars:
    :return:
    '''

def exists_forall_learner(composition, spec_contract, rel_spec_ports,
                          ref_formulas, all_specs_formula, neg_formula, neg_check,
                          pos_formula, pos_check, neg_ca_formula, neg_ca_check,
                          preamble, left_sides, var_map, component_map, input_variables,
                          location_vars, location_map, terminate_evt, manager,
                          relevant_contracts, parameters, max_depth=None):
    """
    verify refinement formula according to preamble
    :param ref_formula:
    :param preamble:
    :param monitored_variables:
    :param checked_variables:
    :return:
    """

    candidate = None
    l_passed = False
    spec_instance_dict = {Literal('m'): TrueFormula()}
    # full_cex_dict = {Literal('w'): Negation(spec_contract.guarantee_formula)}
    full_cex_dict = {}
    full_neg_ca_cex_dict = {}
    generated_cex = set()
    tested_candidates = None
    all_candidates = None
    inverse_location_vars = {y:x for (x,y) in location_vars.items()}
    do_cex_checks = True
    i = 0
    all_s_variables = set([p for p in spec_contract.ports_dict.values()])
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
    num_left = total

    # all_spec_assumptions = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), [x.assume_formula for x in spec_list])
    # c_assumptions = composition.assume_formula
    #
    # all_assumptions = Conjunction(all_spec_assumptions, c_assumptions, merge_literals=False)

    if preamble is None:
        #no extra connections, we try directly if the composition works

        for ref_formula in ref_formulas:
            # ref_formula = build_formulas_for_other_spec(connected_spec, spec, composition)
            l_passed = verify_tautology(ref_formula, return_trace=False)

            if not l_passed:
                break
        LOG.debug("no preamble")
        LOG.debug(l_passed)
        return l_passed, None, None, None
    else:

        # left = Conjunction(preamble, left_sides, merge_literals=False)
        # autf = Conjunction(left, neg_formula, merge_literals=False)


        loc_limits = []
        for loc, lmap in location_map.items():
            a = Geq(loc, Constant(-1))
            b = Leq(loc, Constant(len(lmap)-1))
            loc_limits.append(Conjunction(a, b, merge_literals=False))

        loc_c = None
        if len(loc_limits) > 0:
            loc_c = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), loc_limits)


        ##build positive automaton
        #pos_autsign, pos_aut = build_smv_module(pos_formula, location_vars.values()+lev_map.values(), prefix='1')

        ##build neg assumpt automaton
        #neg_ca_autsign, neg_ca_aut = build_smv_module(neg_ca_formula, location_vars.values()+lev_map.values(), prefix='2')

        # use_constraints = []
        # for var in lev_map.values():
        #     use_constraints.append(Equivalence(var, Constant(-1)))
        #
        # while len(use_constraints) > 0:
        #     # start with only one
        #     use_constraints = use_constraints[:-1]
        #
        #     if len(use_constraints) > 0:
        #         use_cf = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), use_constraints)
        #     else:
        #         use_cf = None
        #
        #     LOG.debug("INCREASE SET")
        #     LOG.debug(use_constraints)


        curr_depth = 0
        first_loop = True

        while first_loop or (max_depth is not None and curr_depth < max_depth):
            first_loop = False
            curr_depth += 1

            depth_constr = []
            depth_f = None
            # define max depth
            if max_depth is not None:
                for v in component_map.values():
                    depth_constr.append(Lt(v, Constant(curr_depth)))

                depth_f = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), depth_constr)

            LOG.debug(preamble)
            LOG.debug(neg_formula)



            left = Conjunction(preamble, left_sides, merge_literals=False)


            if max_depth is not None:
                left = Conjunction(depth_f, left, merge_literals=False)
                LOG.debug("SOLVING FOR DEPTH %d" % curr_depth)

            all_f = Implication(left, neg_formula, merge_literals=False)
            # all_f = Implication(left_sides, neg_formula, merge_literals=False)

            # t,_ = verify_tautology(neg_formula)

            # LOG.debug(all_f)
            autsign, aut = build_smv_module(all_f, location_vars.values() + component_map.values() + param_list,
                                            prefix='0')


            while True:
                if terminate_evt.is_set():
                    return False, None, None, None

                # cex_str_list = ['(%s)' % cex.generate(symbol_set=NusmvSymbolSet,
                #                                       prefix='%s.'%m.unique_name,
                #                                       ignore_precedence=True)
                #                         for m, cex in spec_instance_dict.items()]
                #
                #
                # cex_str = ' & '.join(cex_str_list)

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
                if loc_c is not None:
                    left = Conjunction(loc_c, left, merge_literals=False)

                left = left.generate(symbol_set=NusmvSymbolSet, ignore_precedence=True)

                # base_spec_str = '((' + left + ') & (%s))' % cex_str
                # base_spec_str = base_spec_str + ' -> (%s)' % checks_str
                base_spec_str = "(%s) -> (%s)" % (left, checks_str)


                # #positive checks
                # if len(full_cex_dict) > 0:
                #     pos_cex_str_list = [(w, cex.generate(symbol_set=NusmvSymbolSet, prefix='%s.' % w.unique_name))
                #                     for w, cex in full_cex_dict.items()]
                #
                #     pos_checks_list = ['((%s) -> %s)' % (cex_str, Globally(pos_check).generate(symbol_set=NusmvSymbolSet, prefix='%s.' % w.unique_name))
                #                    for w, cex_str in pos_cex_str_list]
                #
                #     pos_cex_str = ' | '.join(pos_checks_list)
                #
                #     base_spec_str = '(%s) | %s' % (base_spec_str, pos_cex_str)
                #
                # # negative comp assumption bit
                # if len(full_neg_ca_cex_dict) > 0:
                #     neg_ca_cex_str_list = [(x, cex.generate(symbol_set=NusmvSymbolSet, prefix='%s.' % x.unique_name))
                #                     for x, cex in full_neg_ca_cex_dict.items()]
                #
                #     neg_ca_checks_list = ['((%s) -> %s)' % (cex_str, Globally(neg_ca_check).generate(symbol_set=NusmvSymbolSet, prefix='%s.' % x.unique_name))
                #                    for x, cex_str in neg_ca_cex_str_list]
                #
                #     neg_ca_cex_str = ' | '.join(neg_ca_checks_list)
                #
                #     base_spec_str = '(%s) | %s' % (base_spec_str, neg_ca_cex_str)

                # smv = build_smv_program(autsign, aut, location_vars.values()+lev_map.values()+param_list,
                #                         spec_instance_dict.keys(), base_spec_str)

                smv = build_smv_program(autsign, aut, location_vars.values() + component_map.values() + param_list,
                                        spec_instance_dict.keys(), base_spec_str, all_cex_modules, all_cex_names)

                LOG.debug(smv)
                #l_passed, ntrace = verify_candidate(left, neg_formula)
                # LOG.debug(ntrace)
                l_passed, ntrace = verify_tautology_smv(smv, return_trace=True)
                # LOG.debug(ntrace)
                if l_passed:
                    # LOG.debug(smv)
                    # LOG.debug(cex)
                    # LOG.debug(ntrace)
                    # LOG.debug(trace)
                    # LOG.debug(neg_formula)
                    break
                    # return False, None, None, None

                # LOG.debug(ntrace)
                #analyze trace to derive possible solution
                all_locs = trace_analysis_for_loc(ntrace, location_vars.values())
                uses = trace_analysis_for_loc(ntrace, component_map.values())
                param_assign = trace_analysis_for_loc(ntrace, param_list)
                LOG.debug(uses)
                LOG.debug(all_locs)
                LOG.debug(param_assign)


                locs, used_contracts = detect_reject_list(all_locs, location_vars, location_map,
                                          set(spec_contract.output_ports_dict.values()) & rel_spec_ports)
                LOG.debug(locs)

                LOG.debug(location_map)

                #which components are really used?
                #remove spec from list
                used_contracts = used_contracts - {spec_contract}

                really_used = {component_map[c] for c in used_contracts}
                used_f = []
                for var, use in uses.items():
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
                for var, val in locs.items():
                    lconstr.append(Equivalence(var, Constant(val), merge_literals=False))
                    if val >= 0:
                        # LOG.debug(location_map)
                        port = inverse_location_vars[var]
                        connected_p = location_map[var][val]
                        constr.append(Globally(Equivalence(port.literal, connected_p.literal, merge_literals=False)))

                # process parameters
                for p, v in param_assign.items():
                    lconstr.append(Equivalence(p, Constant(v), merge_literals=False))
                    constr.append(Equivalence(p, Constant(v), merge_literals=False))
                #done

                conn = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), constr)
                lconn = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), lconstr)
                just_conn = conn
                LOG.debug(just_conn)
                #new cex
                if len(generated_cex) > 0 and do_cex_checks:
                    all_cex = reduce(lambda x,y: Disjunction(x,y, merge_literals=False), generated_cex)
                    all_cex = Negation(all_cex)
                    LOG.debug(all_cex)
                    conn = Conjunction(conn, all_cex, merge_literals=False)

                left = Conjunction(used_f, conn, merge_literals=False)
                # LOG.debug(conn)
                # LOG.debug(all_specs_formula)

                # # TODO: print is destructive!
                # print_model(locs, inverse_location_vars, location_map, spec_contract, relevant_contracts, manager)

                passed, trace = verify_candidate(left, all_specs_formula)

                if not passed:
                    # LOG.debug(trace)
                    # LOG.debug(input_variables)
                    # get counterexample for inputs
                    cex, _ = derive_valuation_from_trace(trace, input_variables, max_horizon=NUXMV_BOUND)
                    fullcex, _ = derive_valuation_from_trace(trace, all_s_variables, max_horizon=NUXMV_BOUND)


                    # if len(spec_instance_dict) == 1 and type(spec_instance_dict.values()[0]) is TrueFormula:
                    #     spec_instance_dict[spec_instance_dict.keys()[0]] = cex
                    # else:
                    #     spec_instance_dict[Literal('m')] = cex

                    # LOG.debug(trace)
                    # LOG.debug(cex_mod)
                    #full_in_cex, _ = derive_inputs_from_trace(trace, input_variables, max_horizon=NUXMV_BOUND)
                    LOG.debug(cex)
                    LOG.debug(fullcex)
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

                    #DONE: add check to make sure cex is agreeing with spec assumptions. Sometimes it does not work...

                    #TODO: check what happens sometimes with recurrent cex. it should not happen to see the same cex multiple times
                    if cex is not None:
                        cex_p = False
                        #check this is not a spurious cex
                        cex_check = Implication(cex, spec_contract.assume_formula, merge_literals=False)
                        valid = verify_tautology(cex_check, return_trace=False)

                        if valid:
                            for c in spec_instance_dict.values():
                                cex_check = Implication(c, cex, merge_literals=False)
                                cex_p = verify_tautology(cex_check, return_trace=False)
                                if cex_p:
                                    LOG.debug('CEX already encoded')
                                    #assert False
                                    break
                            if not cex_p and do_cex_checks:
                                #if we have only the initial case, replace TRUE with the current CEX
                                if len(spec_instance_dict) == 1 and type(spec_instance_dict.values()[0]) is TrueFormula:
                                    spec_instance_dict[spec_instance_dict.keys()[0]] = cex
                                else:
                                    spec_instance_dict[Literal('m')] = cex
                                #spec_instance_dict[Literal('m')] = cex
                                generated_cex.add(cex)
                                LOG.debug(len(spec_instance_dict))
                                cex_name = Literal('cex_inst').unique_name
                                cex_mod = build_module_from_trace(trace, input_variables, cex_name)

                                LOG.debug(cex_mod)
                                all_cex_modules += cex_mod
                                all_cex_names.add(cex_name)
                        else:
                            LOG.debug('Spurious CEX')
                            LOG.debug(cex)
                            # cex, _ = derive_inputs_from_trace(trace, input_variables, max_horizon=NUXMV_BOUND*2)

                    # #check full check is false for spec
                    # fcex_check = Implication(fullcex, spec_contract.guarantee_formula, merge_literals=False)
                    # fcex_p = verify_tautology(fcex_check, return_trace=False)
                    #
                    # if not fcex_p:
                    #     cex_p = False
                    #     for c in full_cex_dict.values():
                    #         cex_check = Implication(c, fullcex, merge_literals=False)
                    #         cex_p = verify_tautology(cex_check, return_trace=False)
                    #         if cex_p:
                    #             LOG.debug('redundant negative example')
                    #             break
                    #     if not cex_p:
                    #         full_cex_dict[Literal('w')] = fullcex
                    #         LOG.debug('adding negative example')
                    #         # LOG.debug(ft)
                    # # else:
                    # #     full_neg_ca_cex_dict[Literal('x')] = fullcex
                    # #     LOG.debug('adding positive input example')
                    #     # LOG.debug(ft)
                    # #generated_cex.add(cex)

                        # #double check
                        # if len(generated_cex) > 1:
                        #     tt = lconn
                        #
                        #     for c in generated_cex - {cex}:
                        #         tt = Conjunction(tt, c, merge_literals=False)
                        #
                        #     tt = Implication(tt, all_specs_formula, merge_literals=False)
                        #
                        #     p,t = verify_tautology(tt, return_trace=True)
                        #
                        #     LOG.debug(p)
                        #     LOG.debug(t)
                        #     assert p

                    if all_candidates is None:
                        all_candidates = lconn
                    else:
                        all_candidates = Disjunction(all_candidates, lconn, merge_literals=False)


                else:
                    left = Conjunction(used_f, just_conn, merge_literals=False)
                    passed, trace = verify_candidate(left, all_specs_formula)

                    if not passed:
                        #do_cex_checks = False
                        LOG.debug('No CEXs')
                        if all_candidates is None:
                            all_candidates = lconn
                        else:
                            all_candidates = Disjunction(all_candidates, lconn, merge_literals=False)

                        continue

                    LOG.debug('FOUND')
                    var_assign = {}
                    for var, val in locs.items():
                        if val >= 0:
                            # LOG.debug(location_map)
                            port = inverse_location_vars[var]
                            connected_p = location_map[var][val]
                            var_assign[port.unique_name] = connected_p.unique_name
                    LOG.debug(var_assign)
                    LOG.debug(param_assign)
                    return passed, conn, var_assign, param_assign


    return  False, None, None, None
    # return (l_passed, trace, checked_variables, monitored, model_map, contracts, composition,
    #         spec_contract, last_iteration)


def detect_reject_list(location_vals, location_vars, location_map, spec_vars):
    '''
    return a list of connections connected to the spec. ignore the spurious connections
    :param location_vals:
    :return:
    '''

    #connected_contracts = set()

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

                for iport in contract.input_ports_dict.values():
                    if iport not in var_dict:
                        port_list.add(iport)
        # else:
        #     LOG.debug(port.unique_name)
        #     LOG.debug(port.contract)

    return (var_dict, used_contracts)

def verify_candidate(candidate, spec):
    '''verify whether a candidate is a good one'''

    _candidate = Implication(candidate, spec, merge_literals=False)

    l_passed, trace = verify_tautology(_candidate, return_trace=True)

    return l_passed, trace




def assemble_checked_vars(trace_diff, monitored_vars, checked_vars):
    """
    Take the trace diff from trace_analysis and updates the checked_vars dict
    :param trace_diff:
    :param connected_contracts:
    :param checked_vars:
    :return:
    """

    # LOG.debug(checked_vars)
    for p in monitored_vars:

        lev, orig_p = monitored_vars[p]['orig']

        for v_p in trace_diff[p]:
            _, old_v_p = monitored_vars[p]['ports'][v_p]
            checked_vars[(lev, orig_p)].add(old_v_p.base_name)

    # LOG.debug(checked_vars)
    return checked_vars


def print_model(locs, inverse_location_vars, location_map, spec_contract, relevant_contracts, manager):
    '''
    calls graphviz and generate a graphical representation of the model
    :return:
    '''
    var_assign = {}
    for var, val in locs.items():
        if val >= 0:
            # LOG.debug(location_map)
            port = inverse_location_vars[var]
            connected_p = location_map[var][val]
            var_assign[port.unique_name] = connected_p.unique_name
    LOG.debug(var_assign)

    # convert names in spec to original spec
    for name, port in spec_contract.ports_dict.items():
        uname = port.unique_name
        orig_port = manager.spec.ports_dict[name]

        if uname in var_assign:
            var_assign[orig_port.base_name] = var_assign[uname]
            var_assign.pop(uname)
        else:
            for name in var_assign:
                if uname == var_assign[name]:
                    var_assign[name] = orig_port.base_name

    composition, connected_spec, contract_inst = \
        manager.build_composition_from_model(None, manager.spec_port_names,
                                             relevant_contracts, var_assign)

    LOG.debug(connected_spec)
    from graphviz_converter import GraphizConverter
    graphviz_conv = GraphizConverter(connected_spec, composition, contract_inst,
                                     filename='_'.join(manager.spec_port_names))
    graphviz_conv.generate_graphviz()
    graphviz_conv.view()