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


def counterexample_analysis(spec_list, output_port_names, model, manager):
    '''
    Analyze the model thorugh a series of counterexample to infer a set of connections which satisfies
    the spec, if one exists
    :param unconnected_spec:
    :param output_port_names:
    :param model:
    :param manager:
    :return:
    '''

    checked_variables = None
    passed = None
    composition = None
    connected_spec = None
    contracts = None

    for spec in spec_list:
        (passed, trace,
         checked_variables, monitored_variables,
         model_map, contracts, composition,
         connected_spec, last_iteration) = one_step_verification(spec, output_port_names,
                                                                   model, manager,
                                                                   checked_variables=checked_variables)

        if not passed:

            checked_variables = trace_analysis(trace, monitored_variables)

            while not last_iteration:
                (passed, trace,
                 checked_variables, monitored_variables,
                 model_map, contracts, composition,
                 connected_spec,
                 last_iteration) = one_step_verification(spec, output_port_names,
                                                                    model, manager,
                                                                    checked_variables=checked_variables)
                if not passed:
                    trace_diff = trace_analysis(trace, monitored_variables)
                    checked_variables = assemble_checked_vars(trace_diff, monitored_variables,
                                                              checked_variables)

            if not passed:
                return False

    # here only if all are true
    return passed, composition, connected_spec, contracts, model_map

def one_step_verification(unconnected_spec, output_port_names, model, manager, checked_variables=None):
    '''
    Build a SMV model and checks if there is any possible alternative set of connections to satisfy the spec.
    We first need to create additional formulas to express flexible connections.
    :return:
    '''

    LOG.debug('IN')

    spec_contract = unconnected_spec.copy()
    working_spec = unconnected_spec.copy()
    formulas = []

    if checked_variables is None:
        checked_variables = set()

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
    model_map, contract_map = manager.lib_model.contract_copies_by_models(models)
    #
    # LOG.debug(model)
    # LOG.debug(model_map)
    # LOG.debug(contract_map)

    contracts = set(model_map.values())

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

            #spec_port_type_class = spec_contract.out_type_map[s_type]

            index = model[mod].as_long()
            i_mod = manager.lib_model.models[index]
            level = manager.lib_model.model_levels[i_mod.get_id()]
            orig_port = manager.lib_model.port_by_index(index)

            other_contract_orig = orig_port.contract
            other_contract = contract_map[(level, other_contract_orig)]

            port = other_contract.ports_dict[orig_port.base_name]

            #check if this port has already a match in checked_variables
            if (-1, orig_spec_port) not in checked_variables:
                checked_variables[(-1, orig_spec_port)] = set()

            #create monitored set
            if (-1, orig_spec_port, spec_port.base_name) not in monitored_variables:
                monitored_variables[(-1, orig_spec_port, spec_port.base_name)] = set()

            p_type = other_contract_orig.port_type[port.base_name]

            #collect all ports with same type
            port_type_class = {x for x in other_contract_orig.out_type_map[p_type]}

            # we need to exclude all the ports already processed
            port_type_class = port_type_class.difference(checked_variables[(-1, orig_spec_port)])

            # LOG.debug(other_contract_orig.out_type_map)
            # LOG.debug(p_type)

            # now we need to generate all the possibilities among these ports,
            # with the spec port under analysis

            # spec_contract.connect_to_port(spec_port, port)
            p0_name = port_type_class.pop()
            p0 = other_contract.ports_dict[p0_name]
            p0_orig = other_contract_orig.ports_dict[p0_name]

            if len(port_type_class) == 0:
                #update model map
                model_map[mod.get_id()] = manager.lib_model.index[level][p0]

                #we do not monitor this variable anymore
                monitored_variables.pop((-1, orig_spec_port, spec_port.base_name))

                #connect
                spec_contract.connect_to_port(spec_port, p0)

            else:
                last_iteration = False

                formula = Globally(Equivalence(spec_port.literal, p0.literal, merge_literals=False))

                other_composition_name = '%s_%d_%s' % (other_contract.unique_name, level,
                                                       p0.base_name)
                #add to monitored
                monitored_variables[(-1, orig_spec_port,
                                     spec_port.base_name)].add((level, p0_orig,
                                                                other_composition_name))

                for p_name in port_type_class:
                    p = other_contract.ports_dict[p_name]
                    orig_port = other_contract_orig.ports_dict[p_name]

                    formula = Disjunction(formula, Globally(Equivalence(spec_port.literal, p.literal,
                                                            merge_literals=False)),
                                          merge_literals=False)

                    other_composition_name = '%s_%d_%s' % (other_contract.unique_name, level,
                                                           p.base_name)
                    # add to monitored
                    monitored_variables[(-1, orig_spec_port,
                                     spec_port.base_name)].add((level, orig_port,
                                                                other_composition_name))

                formulas.append(formula)


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
                port_type_class = port_type_class.difference(checked_variables[(level, old_port)])

                p0_name = port_type_class.pop()
                p0 = other_contract.ports_dict[p0_name]
                p0_orig = other_contract_orig.ports_dict[p0_name]

                if len(port_type_class) == 0:
                    #not monitored anymore
                    monitored_variables.pop((level, old_port, current_p_composition_name))

                    # update model map
                    model_map[p_model.get_id()] = manager.lib_model.index[level][p0]

                    #connect
                    mapping.connect(current_port, p0,
                                    current_p_composition_name)

                    # LOG.debug(current_contract.unique_name)
                    # LOG.debug(other_contract.unique_name)
                    # LOG.debug(current_port.unique_name)
                    # LOG.debug(other_port.unique_name)
                    processed_ports.add(current_port)
                    processed_ports.add(p0)


                else:

                    last_iteration = False

                    formula = Globally(Equivalence(current_port.literal, p0.literal, merge_literals=False))

                    other_composition_name = '%s_%d_%s' % (other_contract.unique_name, other_level,
                                                           other_port.base_name)
                    #add to monitored
                    monitored_variables[(level, old_port,
                                         current_p_composition_name)].add((level, p0_orig,
                                                                           other_composition_name))

                    if current_port not in processed_ports:
                        mapping.add(current_port,
                                    current_p_composition_name)
                        processed_ports.add(current_port)

                    if other_port not in processed_ports:
                        mapping.add(other_port, other_composition_name)
                        processed_ports.add(other_port)

                    for p_name in port_type_class:
                        p = other_contract.ports_dict[p_name]
                        p_orig = other_contract_orig.ports_dict[p_name]

                        formula = Disjunction(formula, Globally(Equivalence(current_port.literal, p.literal,
                                                                            merge_literals=False)),
                                              merge_literals=False)

                        other_composition_name = '%s_%d_%s' % (other_contract.unique_name, other_level,
                                                               p.base_name)
                        # add to monitored
                        monitored_variables[(level, old_port,
                                         current_p_composition_name)].add((level, p0_orig,
                                                                           other_composition_name))

                        if p not in processed_ports:
                            mapping.add(other_port, other_composition_name)
                            processed_ports.add(p)

                    formulas.append(formula)



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
                port_type_class = port_type_class.difference(checked_variables[(level, old_port)])

                p0_name = port_type_class.pop()
                p0 = spec_contract.ports_dict[p0_name]
                p0_orig = manager.spec_contract.ports_dict[p0_name]

                if len(port_type_class) == 0:
                    # update model map
                    model_map[p_model.get_id()] = manager.lib_model.index[level][p0]

                    #not monitored anymore
                    monitored_variables.pop((level, old_port, current_p_composition_name))

                    #connect
                    spec_contract.connect_to_port(p0, current_port)

                else:

                    last_iteration = False

                    formula = Globally(Equivalence(current_port.literal, p0.literal, merge_literals=False))

                    #add to monitored
                    monitored_variables[(level, old_port, current_p_composition_name)].add((-1, p0_orig,
                                                                           p0_name))

                    for p_name in port_type_class:
                        p = spec_contract.ports_dict[p_name]
                        formula = Disjunction(formula, Globally(Equivalence(current_port.literal, p.literal,
                                                                            merge_literals=False)),
                                              merge_literals=False)

                        # add to monitored
                        monitored_variables[(level, old_port, current_p_composition_name)].add((-1, p_orig,
                                                                           p_name))

                    formulas.append(formula)

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

    # neg_ref = Negation(ref_formula)

    if len(formulas) > 0:
        formula = formulas[0]
        l = len(formulas)
        for i in range(1, l):
            formula = Conjunction(formula, formulas[i], merge_literals=False)

        formula = Negation(Implication(formula, ref_formula, merge_literals=False))
        LOG.debug(formula.generate())
    else:
        formula = ref_formula

    l_passed, trace = verify_tautology(formula, return_trace=True)

    LOG.debug(l_passed)
    # LOG.debug(formula.generate())

        # diff = parse_counterexample(trace, monitored)

    if not l_passed:
        #process monitored vars names
        monitored = {}

        for (level, orig_port, name), v_set in monitored_variables.items():

            if name in composition.ports_dict:
                p = composition.ports_dict[name]
            else:
                p = spec_contract.ports_dict[name]

            monitored[p] = {}
            monitored[p]['orig'] = (level, orig_port)
            monitored[p]['ports'] = {}

            for (v_level, v_orig_port, v_name) in v_set:
                if v_name in composition.ports_dict:
                    v_p = composition.ports_dict[v_name]
                else:
                    v_p = spec_contract.ports_dict[v_name]

                monitored[p]['ports'][v_p] = (v_level, v_orig_port)


    else:
        monitored = None

    return (l_passed, trace, checked_variables, monitored, model_map, contracts, composition,
            spec_contract, last_iteration)


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
    diff = {}

    #create structure to record values
    for p in monitored_vars:
        c_vars[p.unique_name]= None
        diff[p] = set()

        for v_p in monitored_vars[p]['ports']:
            c_vars[v_p.unique_name] = None
            diff[p].add(v_p)


    lines = trace.split('\n')

    after_preamble = False
    state = 0
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

                for v_p in monitored_vars[p]:
                    if c_vars[v_p.unique_name] != p_val:
                        diff[p].remove(v_p)



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


    return diff


def assemble_checked_vars(trace_diff, monitored_vars, checked_vars):
    """
    Take the trace diff from trace_analysis and updates the checked_vars dict
    :param trace_diff:
    :param connected_contracts:
    :param checked_vars:
    :return:
    """

    for p in monitored_vars:

        lev, orig_p = monitored_vars[p]['orig']

        for v_p in trace_diff[p]:
            _, old_v_p = monitored_vars[p]['ports'][v_p]
            checked_vars[(lev, orig_p)].add(old_v_p)


    return checked_vars