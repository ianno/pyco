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


def counterexample_analysis(unconnected_spec, output_port_names, model, manager):
    '''
    Build a SMV model and checks if there is any possible alternative set of connections to satisfy the spec.
    We first need to create additional formulas to express flexible connections.
    :return:
    '''

    LOG.debug('IN')

    spec_contract = unconnected_spec.copy()
    working_spec = unconnected_spec.copy()
    formulas = []

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
            # s_type = spec_contract.type_dict[spec_port]

            #spec_port_type_class = spec_contract.out_type_map[s_type]

            index = model[mod].as_long()
            i_mod = manager.lib_model.models[index]
            level = manager.lib_model.model_levels[i_mod.get_id()]
            orig_port = manager.lib_model.port_by_index(index)

            other_contract_orig = orig_port.contract
            other_contract = contract_map[(level, other_contract_orig)]

            port = other_contract.ports_dict[orig_port.base_name]
            p_type = other_contract_orig.port_type[port.base_name]

            #collect all ports with same type
            port_type_class = {x for x in other_contract_orig.out_type_map[p_type]}

            # LOG.debug(other_contract_orig.out_type_map)
            # LOG.debug(p_type)

            # now we need to generate all the possibilities among these ports,
            # with the spec port under analysis

            # spec_contract.connect_to_port(spec_port, port)
            p0_name = port_type_class.pop()
            p0 = other_contract.ports_dict[p0_name]

            if len(port_type_class) == 0:

                spec_contract.connect_to_port(spec_port, p0)

            else:
                formula = Globally(Equivalence(spec_port.literal, p0.literal, merge_literals=False))

                for p_name in port_type_class:
                    p = other_contract.ports_dict[p_name]
                    formula = Disjunction(formula, Globally(Equivalence(spec_port.literal, p.literal,
                                                            merge_literals=False)),
                                          merge_literals=False)

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


                p0_name = port_type_class.pop()
                p0 = other_contract.ports_dict[p0_name]

                if len(port_type_class) == 0:

                    mapping.connect(current_port, p0,
                                    '%s_%d_%s' % (current_contract.unique_name, level,
                                               current_port.base_name))

                    # LOG.debug(current_contract.unique_name)
                    # LOG.debug(other_contract.unique_name)
                    # LOG.debug(current_port.unique_name)
                    # LOG.debug(other_port.unique_name)
                    processed_ports.add(current_port)
                    processed_ports.add(p0)

                else:

                    formula = Globally(Equivalence(current_port.literal, p0.literal, merge_literals=False))

                    if current_port not in processed_ports:
                        mapping.add(current_port,
                                    '%s_%d_%s' % (current_contract.unique_name, level,
                                               current_port.base_name))
                        processed_ports.add(current_port)

                    if other_port not in processed_ports:
                        mapping.add(other_port, '%s_%d_%s' % (other_contract.unique_name, other_level,
                                                           other_port.base_name))
                        processed_ports.add(other_port)

                    for p_name in port_type_class:
                        p = other_contract.ports_dict[p_name]
                        formula = Disjunction(formula, Globally(Equivalence(current_port.literal, p.literal,
                                                                            merge_literals=False)),
                                              merge_literals=False)

                        if p not in processed_ports:
                            mapping.add(other_port, '%s_%d_%s' % (other_contract.unique_name, other_level,
                                                                  p.base_name))
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

                p0_name = port_type_class.pop()
                p0 = spec_contract.ports_dict[p0_name]

                if len(port_type_class) == 0:
                    spec_contract.connect_to_port(p0, current_port)

                else:

                    formula = Globally(Equivalence(current_port.literal, p0.literal, merge_literals=False))

                    for p_name in port_type_class:
                        p = spec_contract.ports_dict[p_name]
                        formula = Disjunction(formula, Globally(Equivalence(current_port.literal, p.literal,
                                                                            merge_literals=False)),
                                              merge_literals=False)

                    formulas.append(formula)

                if not spec_port.is_input:
                    assert False

    #if there is at least one additional option, keep going, otherwise quit
    if len(formulas) > 0:
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

        formula = formulas[0]
        l = len(formulas)
        for i in range(1, l):
            formula = Conjunction(formula, formulas[i], merge_literals=False)

        # get refinement formula
        verifier = NuxmvRefinementStrategy(composition)

        ref_formula = verifier.get_refinement_formula(spec_contract)

        # neg_ref = Negation(ref_formula)

        formula = Negation(Implication(formula, ref_formula, merge_literals=False))
        LOG.debug(formula.generate())

        l_passed, trace = verify_tautology(formula, return_trace=True)

        LOG.debug(l_passed)
        # LOG.debug(formula.generate())

        if l_passed:
            assert False
        if not l_passed:

            # build monitored vars dict
            # monitored = {}
            #
            # for name in unknowns:
            #     monitored[composition.ports_dict['1_' + name].unique_name] = name
            #     monitored[w_spec.ports_dict[name].unique_name] = name

            # LOG.debug(composition)
            # LOG.debug(cluster)
            # LOG.debug(unknowns)
            # LOG.debug(done)
            # LOG.debug(monitored)
            LOG.debug(trace)

            # diff = parse_counterexample(trace, monitored)
    else:
        return False

    # assert False
