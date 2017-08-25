'''
This module implements the functions necessary to learn from the verifier whether there
exist a port swap that can satisfy the spec.
If so, a counterexample is generated and analyzed to infer the correct connections.

Author: Antonio Iannopollo
'''

from pyco import LOG
from pyco.contract import CompositionMapping
from pycolite.formula import Globally, Equivalence, Disjunction, Implication, Negation, Conjunction
from pycolite.nuxmv import NuxmvRefinementStrategy, verify_tautology


def counterexample_analysis(spec_list, output_port_names, model, manager, terminate_evt):
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

    for spec in spec_list:

        if terminate_evt.is_set():
            return False, composition, connected_spec, contracts, model_map

        if first:
            first = False
            first_spec = spec

            (contracts, composition, connected_spec,
             ref_formula, preamble, monitored,
             checked_variables, model_map) = process_model(spec, output_port_names, rel_spec_ports,
                                                         model, manager, checked_variables=None)

            # from graphviz_converter import GraphizConverter
            # graphviz_conv = GraphizConverter(connected_spec, composition, contracts)
            # graphviz_conv.generate_graphviz()
            # graphviz_conv.view()

        else:
            ref_formula, spec_map = build_formulas_for_other_spec(connected_spec, spec, composition)


        passed, candidate, new_preamble, var_assign = exists_forall_learner(ref_formula, preamble, None, monitored)

        while not passed:
            if terminate_evt.is_set():
                return False, composition, connected_spec, contracts, model_map

            if candidate is None:
                #nope, not found
                # LOG.debug('nope')
                return False, composition, connected_spec, contracts, model_map

            else:

                # LOG.debug(candidate.generate())

                passed, candidate, new_preamble, var_assign = exists_forall_learner(ref_formula, new_preamble, None, monitored)

        preamble = new_preamble
        # LOG.debug('spec done')



    #if we are here we passed
    #we need to build model map
    LOG.debug('found')

    model_map = build_model_map(connected_spec, output_port_names,  manager, var_assign)

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

    return passed, composition, connected_spec, contracts, model_map


def process_model(unconnected_spec, output_port_names, rel_spec_ports, model, manager, checked_variables=None):
    '''
    Build a SMV model and checks if there is any possible alternative set of connections to satisfy the spec.
    We first need to create additional formulas to express flexible connections.
    :return:
    '''

    # LOG.debug('IN')

    # LOG.debug(checked_variables)

    spec_contract = unconnected_spec.copy()
    working_spec = unconnected_spec.copy()
    formulas = []

    if checked_variables is None:
        checked_variables = {}

    monitored_variables = {}
    model_map = {}

    last_iteration = True

    #now we need to collect all the components connected in chain to the spec output we are considering
    # we start with the model connected to the out
    spec_port_models = [manager.spec_out_dict[name] for name in output_port_names]

    # LOG.debug(model)
    # LOG.debug(output_port_name)

    models, spec_models = manager._infer_relevant_ports_from_model(model, output_port_names)
    #
    # LOG.debug(models)
    # LOG.debug(spec_models)

    # now we get all the contracts related to the models.
    # by construction fetching only the outputs, we have the full set of contracts
    contract_to_model_map, contract_map = manager.lib_model.contract_copies_by_models(models)
    #
    # LOG.debug(model)
    # LOG.debug(model_map)
    # LOG.debug(contract_map)

    contracts = set(contract_to_model_map.values())

    # composition mapping to define new names
    mapping = CompositionMapping(contracts| set([working_spec]))

    #process working spec
    for port in working_spec.ports_dict.values():
        name = port.base_name

        if name not in output_port_names:
            spec_contract.connect_to_port(spec_contract.ports_dict[name], port)

    # start with spec port
    # TODO: maybe remove these checks
    for mod in spec_port_models:
        if model[mod].as_long() != -1:

            name = str(mod)
            spec_port = spec_contract.ports_dict[name]
            orig_spec_port = manager.spec_contract.ports_dict[name]
            # s_type = spec_contract.type_dict[spec_port]

            # spec_port_type_class = spec_contract.out_type_map[s_type]

            index = model[mod].as_long()
            i_mod = manager.lib_model.models[index]
            level = manager.lib_model.model_levels[i_mod.get_id()]
            orig_port = manager.lib_model.port_by_index(index)

            other_contract_orig = orig_port.contract
            other_contract = contract_map[(level, other_contract_orig)]

            port = other_contract.ports_dict[orig_port.base_name]

            # check if this port has already a match in checked_variables
            if (-1, orig_spec_port) not in checked_variables:
                checked_variables[(-1, orig_spec_port)] = set()

            # create monitored set
            if (-1, orig_spec_port, spec_port.base_name) not in monitored_variables:
                monitored_variables[(-1, orig_spec_port, spec_port.base_name)] = set()

            p_type = other_contract_orig.port_type[port.base_name]

            # collect all ports with same type
            port_type_class = {x for x in other_contract_orig.out_type_map[p_type]}

            # we need to exclude all the ports already processed
            if len(checked_variables[(-1, orig_spec_port)]) > 0:
                port_type_class = port_type_class & checked_variables[(-1, orig_spec_port)]

            # port_type_class = port_type_class | {port.base_name}


            assert len(port_type_class) > 0

            if len(port_type_class) == 1:

                # spec_contract.connect_to_port(spec_port, port)
                p0_name = port_type_class.pop()
                p0 = other_contract.ports_dict[p0_name]
                p0_orig = other_contract_orig.ports_dict[p0_name]

                # update model map
                model_map[mod.get_id()] = manager.lib_model.index[level][p0_orig]

                # we do not monitor this variable anymore
                monitored_variables.pop((-1, orig_spec_port, spec_port.base_name))

                # connect
                spec_contract.connect_to_port(spec_port, p0)

            else:

                pivots = []
                for pivot_name in port_type_class:

                    pivot = other_contract.ports_dict[pivot_name]
                    p_orig = other_contract_orig.ports_dict[pivot_name]

                    if pivot in other_contract.relevant_ports:

                        other_composition_name = '%s_%d_%s' % (other_contract.unique_name, level,
                                                               pivot_name)

                        # add to monitored
                        monitored_variables[(-1, orig_spec_port,
                                             spec_port.base_name)].add((level, p_orig,
                                                                        other_composition_name))

                        inner = Globally(Equivalence(spec_port.literal, pivot.literal, merge_literals=False))

                        for o_name in port_type_class - {pivot_name}:
                            op = other_contract.ports_dict[o_name]

                            temp = Negation(Globally(Equivalence(spec_port.literal, op.literal, merge_literals=False)))
                            inner = Conjunction(inner, temp, merge_literals=False)

                        pivots.append(inner)
                if len(pivots) > 0:
                    formula = reduce((lambda x, y: Disjunction(x, y, merge_literals=False)), pivots)
                    formulas.append(formula)

                # preamble = Globally(Equivalence(spec_port.literal, p0.literal, merge_literals=False))
                #
                # other_composition_name = '%s_%d_%s' % (other_contract.unique_name, level,
                #                                        p0_name)
                # #add to monitored
                # monitored_variables[(-1, orig_spec_port,
                #                      spec_port.base_name)].add((level, p0_orig,
                #                                                 other_composition_name))
                #
                # for p_name in port_type_class:
                #     p = other_contract.ports_dict[p_name]
                #     orig_port = other_contract_orig.ports_dict[p_name]
                #
                #     preamble = Disjunction(preamble, Globally(Equivalence(spec_port.literal, p.literal,
                #                                             merge_literals=False)),
                #                           merge_literals=False)
                #
                #     other_composition_name = '%s_%d_%s' % (other_contract.unique_name, level,
                #                                            p_name)
                #     # add to monitored
                #     monitored_variables[(-1, orig_spec_port,
                #                      spec_port.base_name)].add((level, orig_port,
                #                                                 other_composition_name))
                #
                # formulas.append(preamble)


    # connections among candidates
    processed_ports = set()
    for p_model in models | spec_models:
        if model[p_model] is not None:
            level, old_contract = manager.lib_model.contract_by_model(p_model)
            current_contract = contract_map[(level, old_contract)]
            old_port = manager.lib_model.port_by_model(p_model)
            current_port = current_contract.ports_dict[old_port.base_name]
            other_index = model[p_model].as_long()

            current_p_composition_name = '%s_%d_%s' % (current_contract.unique_name, level,
                                               current_port.base_name)

            if (level, old_port, current_p_composition_name) not in monitored_variables:
                monitored_variables[(level, old_port, current_p_composition_name)] = set()

            if (level, old_port) not in checked_variables:
                checked_variables[(level, old_port)] = set()

            if other_index < manager.lib_model.specs_at:

                other_mod = manager.lib_model.models[other_index]
                other_level = manager.lib_model.model_levels[other_mod.get_id()]

                other_port_orig = manager.lib_model.port_by_index(other_index)

                other_contract_orig = other_port_orig.contract
                other_contract = contract_map[(other_level, other_port_orig.contract)]

                other_port = other_contract.ports_dict[other_port_orig.base_name]

                p_type = other_contract_orig.port_type[other_port.base_name]

                # collect all ports with same type
                port_type_class = {x for x in other_contract_orig.out_type_map[p_type]}

                #remove ports already processed
                if len(checked_variables[(level, old_port)]) > 0:
                    port_type_class = port_type_class & checked_variables[(level, old_port)]


                #make sure initial port is always there
                # port_type_class = port_type_class | {other_port.base_name}
                assert len(port_type_class) > 0
                # LOG.debug(port_type_class)
                if len(port_type_class) == 1:

                    p0_name = port_type_class.pop()
                    p0 = other_contract.ports_dict[p0_name]
                    p0_orig = other_contract_orig.ports_dict[p0_name]

                    #not monitored anymore
                    monitored_variables.pop((level, old_port, current_p_composition_name))

                    # update model map
                    model_map[p_model.get_id()] = manager.lib_model.index[level][p0_orig]

                    #connect
                    mapping.connect(current_port, p0,
                                    current_p_composition_name)

                    # LOG.debug(current_contract.unique_name)
                    # LOG.debug(other_contract.unique_name)
                    # LOG.debug(current_port.unique_name)
                    # LOG.debug(p0.unique_name)
                    processed_ports.add(current_port)
                    processed_ports.add(p0)


                else:

                    if current_port not in processed_ports:
                        mapping.add(current_port,
                                    current_p_composition_name)
                        processed_ports.add(current_port)


                    pivots = []
                    for pivot_name in port_type_class:

                        pivot = other_contract.ports_dict[pivot_name]
                        p_orig = other_contract_orig.ports_dict[pivot_name]

                        if pivot in other_contract.relevant_ports:
                            other_composition_name = '%s_%d_%s' % (other_contract.unique_name, other_level,
                                                                   pivot_name)

                            # add to monitored
                            monitored_variables[(level, old_port,
                                             current_p_composition_name)].add((other_level, p_orig,
                                                                               other_composition_name))

                            if pivot not in processed_ports:
                                mapping.add(pivot, other_composition_name)
                                processed_ports.add(pivot)


                            inner = Globally(Equivalence(current_port.literal, pivot.literal, merge_literals=False))

                            for o_name in port_type_class - {pivot_name}:
                                op = other_contract.ports_dict[o_name]

                                temp = Negation(Globally(Equivalence(current_port.literal, op.literal, merge_literals=False)))
                                inner = Conjunction(inner, temp, merge_literals=False)

                            pivots.append(inner)

                    if len(pivots) > 0:
                        formula = reduce((lambda x, y: Disjunction(x, y, merge_literals=False)), pivots)
                        formulas.append(formula)




                    # for p_name in port_type_class:
                    #     p = other_contract.ports_dict[p_name]
                    #     p_orig = other_contract_orig.ports_dict[p_name]
                    #
                    #     preamble = Disjunction(preamble, Globally(Equivalence(current_port.literal, p.literal,
                    #                                                         merge_literals=False)),
                    #                           merge_literals=False)
                    #
                    #     other_composition_name = '%s_%d_%s' % (other_contract.unique_name, other_level,
                    #                                            p_name)
                    #     # add to monitored
                    #     monitored_variables[(level, old_port,
                    #                      current_p_composition_name)].add((level, p_orig,
                    #                                                        other_composition_name))
                    #
                    #     if p not in processed_ports:
                    #         mapping.add(p, other_composition_name)
                    #         processed_ports.add(p)
                    #
                    # formulas.append(preamble)



                # LOG.debug(current_contract.unique_name)
                # LOG.debug(other_contract.unique_name)
                # LOG.debug(current_port.unique_name)
                # LOG.debug(other_port.unique_name)

            else:
                spec_port = spec_contract.ports_dict[manager.lib_model.spec_by_index_map[other_index]]

                p_type = unconnected_spec.port_type[spec_port.base_name]

                # collect all ports with same type
                port_type_class = {x for x in unconnected_spec.in_type_map[p_type]}

                #remove ports already processed
                if len( checked_variables[(level, old_port)]) > 0:
                    port_type_class = port_type_class & checked_variables[(level, old_port)]

                # remove initial port, in case it's there
                assert len(port_type_class) > 0

                if len(port_type_class) == 1:

                    p0_name = spec_port.base_name
                    p0 = spec_port
                    # p0_orig = manager.spec_contract.ports_dict[p0_name]

                    # update model map
                    model_map[p_model.get_id()] = manager.lib_model.spec_map[p0_name]

                    #not monitored anymore
                    monitored_variables.pop((level, old_port, current_p_composition_name))

                    #connect
                    spec_contract.connect_to_port(p0, current_port)

                else:


                    pivots = []
                    for pivot_name in port_type_class:
                        pivot = spec_contract.ports_dict[pivot_name]
                        p_orig = unconnected_spec.ports_dict[pivot_name]

                        if pivot in rel_spec_ports:
                            # add to monitored
                            monitored_variables[(level, old_port,
                                             current_p_composition_name)].add((-1, p_orig,
                                                                               pivot_name))


                            inner = Globally(Equivalence(current_port.literal, pivot.literal, merge_literals=False))

                            for o_name in port_type_class - {pivot_name}:
                                op = spec_contract.ports_dict[o_name]

                                temp = Negation(Globally(Equivalence(current_port.literal, op.literal, merge_literals=False)))
                                inner = Conjunction(inner, temp, merge_literals=False)

                            pivots.append(inner)

                    if len(pivots) > 0:
                        formula = reduce((lambda x, y: Disjunction(x, y, merge_literals=False)), pivots)
                        formulas.append(formula)


                    # preamble = Globally(Equivalence(current_port.literal, p0.literal, merge_literals=False))
                    #
                    # #add to monitored
                    # monitored_variables[(level, old_port, current_p_composition_name)].add((-1, p0_orig,
                    #                                                        p0_name))
                    #
                    # for p_name in port_type_class:
                    #     p = spec_contract.ports_dict[p_name]
                    #     p_orig = manager.spec_contract.ports_dict[p_name]
                    #
                    #     preamble = Disjunction(preamble, Globally(Equivalence(current_port.literal, p.literal,
                    #                                                         merge_literals=False)),
                    #                           merge_literals=False)
                    #
                    #     # add to monitored
                    #     monitored_variables[(level, old_port, current_p_composition_name)].add((-1, p_orig,
                    #                                                        p_name))
                    #
                    # formulas.append(preamble)

                if not spec_port.is_input:
                    assert False


    # add all the remaining names to new composition
    for (level, old_contract) in contract_map.keys():
        for old_port in old_contract.ports_dict.values():
            current_contract = contract_map[(level, old_contract)]
            current_port = current_contract.ports_dict[old_port.base_name]
            if current_port not in processed_ports:
                mapping.add(current_port, '%s_%d_%s' % (current_contract.unique_name,
                                                        level,
                                                     current_port.base_name))
                processed_ports.add(current_port)

    # for contract in contracts:
    #    LOG.debug(contract)
    # LOG.debug(working_spec)
    # LOG.debug(spec_contract)

    # if not complete_model:
    #    c_set = self.filter_candidate_contracts_for_composition(contracts, spec_contract)

    # compose
    #root = contracts.pop()

    # c_set.add(root.copy())

    composition = working_spec.compose(contracts, composition_mapping=mapping)

    # get refinement formula
    verifier = NuxmvRefinementStrategy(composition)
    ref_formula = verifier.get_refinement_formula(spec_contract)
    # LOG.debug(spec_contract)
    # LOG.debug(ref_formula.generate())
    if len(formulas) > 0:

        preamble = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), formulas)

        # formula = Implication(formula, ref_formula, merge_literals=False)
        # LOG.debug(formula.generate())
    else:
        preamble = None

    # process monitored vars names
    monitored = {}

    for (level, orig_port, name), v_set in monitored_variables.items():

        #keep the following order. it matters because of working spec
        if name in spec_contract.ports_dict:
            p = spec_contract.ports_dict[name]
        else:
            p = composition.ports_dict[name]


        # LOG.debug(p.unique_name)
        monitored[p] = {}
        monitored[p]['orig'] = (level, orig_port)
        monitored[p]['ports'] = {}

        for (v_level, v_orig_port, v_name) in v_set:
            if v_name in composition.ports_dict:
                v_p = composition.ports_dict[v_name]
            else:
                v_p = spec_contract.ports_dict[v_name]

            monitored[p]['ports'][v_p] = (v_level, v_orig_port)

    return contracts, composition, spec_contract, ref_formula, preamble, monitored, checked_variables, model_map


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

                    assert len(var_assign[(orig_lev, orig_port)]) == 1
                    c_level, c_port = var_assign[(orig_lev, orig_port)].pop()

                    model_map[mod.get_id()] = manager.lib_model.index[c_level][c_port]


        else:
            mod = manager.lib_model.model_by_port(orig_port)[orig_lev]

            assert len(var_assign[(orig_lev, orig_port)]) == 1
            c_level, c_port = var_assign[(orig_lev, orig_port)].pop()

            if c_level > -1:
                model_map[mod.get_id()] = manager.lib_model.index[c_level][c_port]

                # LOG.debug(manager.lib_model.index[c_level][c_port])
                # LOG.debug(manager.lib_model.port_by_index(manager.lib_model.index[c_level][c_port]).base_name)
            else:
                model_map[mod.get_id()] = manager.lib_model.spec_map[orig_port.base_name]

    # LOG.debug(model_map)
    return model_map



def build_formulas_for_other_spec(connected_spec, spec_contract, composition, monitored_vars=None):

    spec_map = []

    for p_name in connected_spec.ports_dict:
        # spec_map.append(Equivalence(spec_contract.ports_dict[p_name].literal, connected_spec.ports_dict[p_name].literal, merge_literals=False))

        connected_spec.connect_to_port(connected_spec.ports_dict[p_name], spec_contract.ports_dict[p_name])
    # if len(spec_map) > 0:
    #     spec_formula = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), spec_map)
    # else:
    #     spec_formula = None

    # get refinement formula
    verifier = NuxmvRefinementStrategy(composition)
    ref_formula = verifier.get_refinement_formula(spec_contract)

    # old_rel_names = [p.base_name for p in connected_spec.relevant_ports]
    # new_rel_names = [p.base_name for p in spec_contract.relevant_ports]
    #
    # #process monitored vars
    # for p in monitored_vars:
    #
    #     for vp in monitored_vars['ports']:
    #
    #         if vp.bas

    return ref_formula, None
    # neg_ref = Negation(ref_formula)



#TODO: case in which preamble is None

def exists_forall_learner(ref_formula, preamble, spec_map, monitored_variables):
    """
    verify refinement formula according to preamble
    :param ref_formula:
    :param preamble:
    :param monitored_variables:
    :param checked_variables:
    :return:
    """

    candidate = None

    if spec_map is not None:
        updated_preamble = Conjunction(preamble, spec_map, merge_literals=False)
    else:
        updated_preamble = preamble


    if updated_preamble is  None:
        l_passed = verify_tautology(ref_formula, return_trace=False)

        return l_passed, None, None, {}
    else:
        neg_ref = Negation(ref_formula)
        formula = Implication(updated_preamble, neg_ref, merge_literals=False)


        # LOG.debug(formula.generate())
        l_passed, trace = verify_tautology(formula, return_trace=True)

        # LOG.debug(l_passed)
        print('.'),
        # LOG.debug(formula.generate())

            # diff = parse_counterexample(trace, monitored)


        if l_passed:
            #if this passes, it means that we are done. we could find an assignment that makes the formula false,
            # or the formula is always false for any possible connection
            return False, candidate,preamble, None

        else:
            var_assign, ret_assign = trace_analysis(trace, monitored_variables)

            #build constraints from var assignment
            v_assign = []

            for p in var_assign:
                for v_p in var_assign[p]:
                    v_assign.append(Globally(Equivalence(p.literal, v_p.literal, merge_literals=False)))


            candidate = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), v_assign)

            if spec_map is not None:
                mapped = Conjunction(candidate, spec_map, merge_literals=False)
            else:
                mapped = candidate


            #now check if candidate is a good solution:
            sol_verif = Implication(mapped, ref_formula, merge_literals=False)

            l_passed, trace = verify_tautology(sol_verif, return_trace=True)


            # LOG.debug(preamble.generate())
            # LOG.debug(updated_preamble.generate())
            # LOG.debug(candidate.generate())
            #
            # for p in monitored_variables:
            #     LOG.debug(p.base_name)
            #     LOG.debug(p.unique_name)
            #     LOG.debug('--')
            #     for v in monitored_variables[p]['ports']:
            #         LOG.debug('.')
            #         LOG.debug(v.base_name)
            #         LOG.debug(v.unique_name)
            #     LOG.debug('++')


            new_preamble = Conjunction(preamble, Negation(candidate), merge_literals=False)

            if l_passed:
                #we are done
                # LOG.debug(candidate.generate())
                # LOG.debug(var_assign)
                return l_passed, candidate, new_preamble, ret_assign
            else:
                #otherwise build the new preamble
                return l_passed, candidate, new_preamble, ret_assign



    # return (l_passed, trace, checked_variables, monitored, model_map, contracts, composition,
    #         spec_contract, last_iteration)


def trace_analysis(trace, monitored_vars):
    """
    Analyize the counterexample trace to infer wrong connections
    :param monitored_vars:
    :return:
    :param trace:
    :param checked_variables:
    :return:
    """
    # diff = set()
    # c_vars = {p.base_name: {} for p in monitored_vars.keys()}
    #
    # for u_name, b_name in monitored_vars.items():
    #     c_vars[b_name][u_name] = None

    c_vars = {}
    var_assign = {}

    # LOG.debug(trace)
    # LOG.debug(monitored_vars)

    #create structure to record values

    # #process only the first one
    # p = monitored_vars.keys()[0]
    for p in monitored_vars:
        # LOG.debug(p.base_name)
        # LOG.debug(p.unique_name)
        c_vars[p.unique_name]= None
        var_assign[p] = set()

        for v_p in monitored_vars[p]['ports']:
            # LOG.debug(v_p.base_name)
            # LOG.debug(v_p.unique_name)
            c_vars[v_p.unique_name] = None
            var_assign[p].add(v_p)


    # LOG.debug(c_vars)
    lines = trace.split('\n')

    after_preamble = False

    for line in lines:
        line = line.strip()

        # LOG.debug(line)

        if not after_preamble:
            if not line.startswith('->'):
                continue
            else:
                after_preamble = True
                # LOG.debug('after preamble')

        # done with the preamble
        # analyze state by state
        if line.startswith('->'):
            # new state, check consistency among vars
            # LOG.debug(c_vars)
            for p in monitored_vars:

                p_val = c_vars[p.unique_name]

                for v_p in monitored_vars[p]['ports']:
                    if v_p in var_assign[p] and c_vars[v_p.unique_name] != p_val:
                        # LOG.debug('remove')
                        # LOG.debug(p.unique_name)
                        # LOG.debug(p_val)
                        # LOG.debug(v_p.unique_name)
                        # LOG.debug(c_vars[v_p.unique_name])
                        var_assign[p].remove(v_p)

            # LOG.debug(diff)



        elif line.startswith('--'):
            # indicates loop in trace, skip line
            pass
        else:
            line_elems = line.split('=')
            line_elems = [l.strip() for l in line_elems]

            # LOG.debug(line_elems)
            # LOG.debug(c_vars)

            if line_elems[0] in c_vars:
                # base_n = monitored_vars[line_elems[0]]

                if line_elems[1] == 'TRUE':
                    val = True
                else:
                    val = False

                c_vars[line_elems[0]] = val

    # for c in var_assign:
    #     LOG.debug('**')
    #     LOG.debug(c.base_name)
    #     LOG.debug(c.unique_name)
    #     assert len(var_assign[c])==1
    #     for v in var_assign[c]:
    #         LOG.debug('.')
    #         LOG.debug(v.base_name)
    #         LOG.debug(v.unique_name)


    #return assignement
    ret_assign = {}

    for p in var_assign:
        orig_level, orig_port = monitored_vars[p]['orig']
        ret_assign[(orig_level, orig_port)] = set()

        for v in var_assign[p]:
            origv_level, origv_port = monitored_vars[p]['ports'][v]
            ret_assign[(orig_level, orig_port)].add((origv_level, origv_port))

    return var_assign, ret_assign


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