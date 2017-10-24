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
                                Constant, Eventually, Until)
from pycolite.nuxmv import NuxmvRefinementStrategy, verify_tautology
from pycolite.parser.parser import LTL_PARSER
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




def counterexample_analysis(spec_list, output_port_names, model, manager, pid,
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

    rel_spec_ports = set()
    for spec in spec_list:
        rel_spec_ports |= spec.relevant_ports

    print('*'),
    # spec = spec_list[0]
    # (contracts, composition, connected_spec,
    #  ref_formula, preamble, monitored, model_map) = process_model(spec, output_port_names, rel_spec_ports,
    #                                                               model, manager)
    #
    # return False, composition, connected_spec, contracts, model_map
    if terminate_evt.is_set():
        return False, composition, connected_spec, contracts, model_map

    (contracts, compositions, connected_spec,
     ref_formulas, neg_formula, preamble, left_sides, monitored, model_map) = process_model(spec_list, output_port_names, rel_spec_ports,
                                                     model, manager)

    input_variables = set([p for p in connected_spec.input_ports_dict.values()])


        # from graphviz_converter import GraphizConverter
        # graphviz_conv = GraphizConverter(connected_spec, composition, contracts)
        # graphviz_conv.generate_graphviz()
        # graphviz_conv.view()

    # else:
    #     #other specs have different unique names
    #     # LOG.debug('here')
    #     ref_formula = build_formulas_for_other_spec(connected_spec, spec, composition)


    #performs first step of learning loo?p
    passed, candidate, new_preamble, var_assign = exists_forall_learner(ref_formulas, neg_formula, preamble, left_sides, monitored, input_variables, terminate_evt)
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

    # preamble = new_preamble
    # LOG.debug('spec done')



    #if we are here we passed
    #we need to build model map
    # LOG.debug('found')

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


    if passed:
        LOG.debug('done')
        result_queue.put((pid, frozenset(model_map.items())))
        found_event.set()
        terminate_evt.set()

    return passed


def process_model(spec_list, output_port_names, relevant_spec_ports,
                   model, manager):
    '''
    Build a SMV model and checks if there is any possible alternative set of connections to satisfy the spec.
    We first need to create additional formulas to express flexible connections.
    :return:
    '''

    # LOG.debug('IN')

    # LOG.debug(checked_variables)

    unconnected_spec = spec_list[0]
    spec_contract = unconnected_spec.copy()
    working_specs = {s.unique_name: s.copy() for s in spec_list}
    formulas = []


    # if checked_variables is None:
    #     checked_variables = {}

    monitored_variables = {}
    model_map = {}

    #now we need to collect all the components connected in chain to the spec output we are considering
    # we start with the model connected to the out
    spec_port_models = [manager.spec_out_dict[name] for name in output_port_names]

    # LOG.debug(model)
    # LOG.debug(output_port_names)

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
    # mapping = CompositionMapping(contracts| set([working_spec]))
    mappings = {s.unique_name: CompositionMapping(contracts | {working_specs[s.unique_name]}) for s in spec_list}

    #process working spec
    for ws in working_specs.values():
        for port in ws.ports_dict.values():
            name = port.base_name

            if name not in output_port_names:
                spec_contract.connect_to_port(spec_contract.ports_dict[name], port)

    # start with spec port
    # TODO: maybe remove these checks
    for mod in spec_port_models:
        if model[mod].as_long() != -1:

            name = str(mod)

            if name in output_port_names:
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

                # create monitored set
                if (-1, orig_spec_port, spec_port.base_name) not in monitored_variables:
                    monitored_variables[(-1, orig_spec_port, spec_port.base_name)] = set()

                p_type = other_contract_orig.port_type[port.base_name]

                # collect all ports with same type
                port_type_class = {x for x in other_contract_orig.out_type_map[p_type]}

                # port_type_class = port_type_class | {port.base_name}


                assert len(port_type_class) > 0

                #if size is 1, connect directly
                if len(port_type_class) == 1:

                    # spec_contract.connect_to_port(spec_port, port)
                    p0_name = port_type_class.pop()
                    p0 = other_contract.ports_dict[p0_name]
                    p0_orig = other_contract_orig.ports_dict[p0_name]

                    # update model map
                    model_map[mod.get_id()] = manager.lib_model.index[p0_orig][level]

                    # we do not monitor this variable anymore
                    monitored_variables.pop((-1, orig_spec_port, spec_port.base_name))

                    # connect
                    spec_contract.connect_to_port(spec_port, p0)

                #else add variables in monitored list
                else:

                    pivots = []
                    for pivot_name in port_type_class:

                        pivot = other_contract.ports_dict[pivot_name]
                        p_orig = other_contract_orig.ports_dict[pivot_name]

                        # if pivot in other_contract.relevant_ports:

                        other_composition_name = '%s_%d_%s' % (other_contract.unique_name, level,
                                                               pivot_name)

                        # add to monitored
                        monitored_variables[(-1, orig_spec_port,
                                             spec_port.base_name)].add((level, p_orig,
                                                                        other_composition_name))

                        inner = Globally(Equivalence(spec_port.literal, pivot.literal, merge_literals=False))

                        # for o_name in port_type_class - {pivot_name}:
                        #     op = other_contract.ports_dict[o_name]
                        #
                        #     temp = Negation(Globally(Equivalence(spec_port.literal, op.literal, merge_literals=False)))
                        #     inner = Conjunction(inner, temp, merge_literals=False)

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

            # if (level, old_port) not in checked_variables:
            #     checked_variables[(level, old_port)] = set()

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

                # #remove ports already processed
                # if len(checked_variables[(level, old_port)]) > 0:
                #     port_type_class = port_type_class & checked_variables[(level, old_port)]


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
                    model_map[p_model.get_id()] = manager.lib_model.index[p0_orig][level]

                    #connect
                    for m in mappings.values():
                        m.connect(current_port, p0,
                                        current_p_composition_name)

                    # LOG.debug(current_contract.unique_name)
                    # LOG.debug(other_contract.unique_name)
                    # LOG.debug(current_port.unique_name)
                    # LOG.debug(p0.unique_name)
                    processed_ports.add(current_port)
                    processed_ports.add(p0)


                else:

                    if current_port not in processed_ports:
                        for m in mappings.values():
                            m.add(current_port,
                                    current_p_composition_name)

                        processed_ports.add(current_port)


                    pivots = []
                    for pivot_name in port_type_class:

                        pivot = other_contract.ports_dict[pivot_name]
                        p_orig = other_contract_orig.ports_dict[pivot_name]

                        # if pivot in other_contract.relevant_ports:
                        other_composition_name = '%s_%d_%s' % (other_contract.unique_name, other_level,
                                                               pivot_name)

                        # add to monitored
                        monitored_variables[(level, old_port,
                                         current_p_composition_name)].add((other_level, p_orig,
                                                                           other_composition_name))

                        if pivot not in processed_ports:
                            for m in mappings.values():
                                m.add(pivot, other_composition_name)

                            processed_ports.add(pivot)


                        inner = Globally(Equivalence(current_port.literal, pivot.literal, merge_literals=False))

                        # for o_name in port_type_class - {pivot_name}:
                        #     op = other_contract.ports_dict[o_name]
                        #
                        #     temp = Negation(Globally(Equivalence(current_port.literal, op.literal, merge_literals=False)))
                        #     inner = Conjunction(inner, temp, merge_literals=False)

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

                # #remove ports already processed
                # if len( checked_variables[(level, old_port)]) > 0:
                #     port_type_class = port_type_class & checked_variables[(level, old_port)]

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

                        #if pivot in relevant_spec_ports:
                        # add to monitored
                        monitored_variables[(level, old_port,
                                         current_p_composition_name)].add((-1, p_orig,
                                                                           pivot_name))


                        inner = Globally(Equivalence(current_port.literal, pivot.literal, merge_literals=False))

                        # for o_name in port_type_class - {pivot_name}:
                        #     op = spec_contract.ports_dict[o_name]
                        #
                        #     temp = Negation(Globally(Equivalence(current_port.literal, op.literal, merge_literals=False)))
                        #     inner = Conjunction(inner, temp, merge_literals=False)

                        pivots.append(inner)
                        # LOG.debug(inner.generate())

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
                for m in mappings.values():
                    m.add(current_port, '%s_%d_%s' % (current_contract.unique_name,
                                                        level, current_port.base_name))

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

    compositions = {s.unique_name: working_specs[s.unique_name].compose(contracts, composition_mapping=mappings[s.unique_name])
                    for s in spec_list}

    #make compositions port names uniform
    for c1 in compositions.values():
        for c2 in compositions.values():
            for p_name in c1.ports_dict:
                c1.connect_to_port(c1.ports_dict[p_name], c2.ports_dict[p_name])


    # get refinement formula
    # verifier = NuxmvRefinementStrategy(composition)
    # ref_formula = verifier.get_refinement_formula(spec_contract)
    # LOG.debug(spec_contract)
    # LOG.debug(ref_formula.generate())


    ref_formulas = [build_formulas_for_other_spec(spec_contract, s, compositions[s.unique_name]) for s in spec_list]
    # ref_formula = build_formula_for_all_specs(spec_contract, spec_list, composition)
    neg_formula = build_neg_formula_for_all_specs(spec_contract, spec_list, compositions)

    # neg_formula = Negation(reduce(lambda x, y: Conjunction(x, y, merge_literals=False), ref_formulas))

    left_sides = TrueFormula()

    if len(formulas) > 0:

        preamble = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), formulas)

        # formula = Implication(formula, ref_formula, merge_literals=False)
        # LOG.debug(preamble.generate())

        # ref_a = Negation(composition.assume_formula)
        # ref_a1 = Conjunction(preamble, spec_contract.assume_formula, merge_literals=False)
        # impl2 = Implication(ref_a1, ref_a, merge_literals=False)
        #
        # ref = Negation(spec_contract.guarantee_formula)
        #
        # ref = Implication(composition.guarantee_formula, ref, merge_literals=False)


        # ref1 = spec_contract.guarantee_formula
        # ref1 = Negation(Implication(composition.guarantee_formula, ref1, merge_literals=False))

        # ref = Disjunction(ref, ref1, merge_literals=False)

        for c in compositions.values():
            left_sides = Conjunction(left_sides, c.guarantee_formula, merge_literals=False)

        for s in spec_list:
            left_sides = Conjunction(left_sides, s.assume_formula, merge_literals=False)


        # preamble = Conjunction(preamble, composition.guarantee_formula, merge_literals=False)
        # preamble = Conjunction(preamble, spec_contract.assume_formula, merge_literals=False)


        # for spec in spec_list:
        #     preamble = Conjunction(preamble, spec.assume_formula, merge_literals=False)

        # ref1 = Negation(ref_formula)
        #
        # impl = Implication(ref, ref1, merge_literals=False)
        #
        # # cc = Conjunction(impl, impl2, merge_literals=False)
        #
        # l_passed, trace = verify_tautology(impl, return_trace=True)


    else:
        preamble = None

    # for c in compositions.values():
    #     LOG.debug(c)

    # LOG.debug(spec_contract)



    # LOG.debug(preamble)
    # process monitored vars names
    monitored = {}
    base_composition = compositions.values()[0]

    # from graphviz_converter import GraphizConverter
    # graphviz_conv = GraphizConverter(spec_contract, base_composition, contracts | set([working_specs.values()[0]]))
    # graphviz_conv.generate_graphviz()
    # graphviz_conv.view()

    for (level, orig_port, name), v_set in monitored_variables.items():

        #keep the following order. it matters because of working spec
        if name in spec_contract.ports_dict:
            p = spec_contract.ports_dict[name]
        else:
            p = base_composition.ports_dict[name]


        # LOG.debug(p.unique_name)
        monitored[p] = {}
        monitored[p]['orig'] = (level, orig_port)
        monitored[p]['ports'] = {}

        for (v_level, v_orig_port, v_name) in v_set:
            if v_name in base_composition.ports_dict:
                v_p = base_composition.ports_dict[v_name]
            else:
                v_p = spec_contract.ports_dict[v_name]

            monitored[p]['ports'][v_p] = (v_level, v_orig_port)

    # LOG.debug(monitored)

    return contracts, compositions, spec_contract, ref_formulas, neg_formula, preamble, left_sides, monitored, model_map


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



def build_formulas_for_other_spec(connected_spec, spec_contract, composition):

    for p_name in connected_spec.ports_dict:

        connected_spec.connect_to_port(connected_spec.ports_dict[p_name], spec_contract.ports_dict[p_name])

    verifier = NuxmvRefinementStrategy(composition)
    ref_formula = verifier.get_refinement_formula(spec_contract)

    return ref_formula


def build_neg_formula_for_all_specs(connected_spec, spec_list, compositions):

    spec_map = []

    for spec_contract in spec_list:
        for p_name in connected_spec.ports_dict:
            # spec_map.append(Equivalence(spec_contract.ports_dict[p_name].literal, connected_spec.ports_dict[p_name].literal, merge_literals=False))

            connected_spec.connect_to_port(connected_spec.ports_dict[p_name], spec_contract.ports_dict[p_name])

    #specs_asm = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.assume_formula for s in spec_list])
    specs_gnt = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.guarantee_formula for s in spec_list])

    g_check = specs_gnt
    a_check = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [compositions[s.unique_name].assume_formula for s in spec_list])


    return Negation(Conjunction(a_check, g_check, merge_literals=False))
    # neg_ref = Negation(ref_formula)

def build_formula_for_all_specs(connected_spec, spec_list, composition):

    spec_map = []

    for spec_contract in spec_list:
        for p_name in connected_spec.ports_dict:
            # spec_map.append(Equivalence(spec_contract.ports_dict[p_name].literal, connected_spec.ports_dict[p_name].literal, merge_literals=False))

            connected_spec.connect_to_port(connected_spec.ports_dict[p_name], spec_contract.ports_dict[p_name])

    #specs_asm = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.assume_formula for s in spec_list])
    specs_gnt = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), [s.guarantee_formula for s in spec_list])

    g_check = Implication(composition.guarantee_formula, specs_gnt, merge_literals=False)
    a_check = Implication(spec_list[0].assume_formula, composition.assume_formula, merge_literals=False)


    return Conjunction(a_check, g_check, merge_literals=False)


def build_formula_for_multiple_inputs(preamble, all_candidates, neg_formula, left_sides, counterexamples, monitored_vars):
    """
    Build a single formula by replicating the model for each counterexample
    and constraining the combinations
    :param formula:
    :param counterexamples:
    :return:
    """

    # new_preamble = preamble
    # new_neg_formula = neg_formula
    if counterexamples is None:
        temp = Conjunction(preamble, left_sides, merge_literals=False)
        formula = Implication(temp, neg_formula, merge_literals=False)
        return formula
    else:
        first = counterexamples[0]

        # new_preamble = Conjunction(preamble, first, merge_literals=False)
        cex = first

        # LOG.debug(cex)
        formula = Implication(cex, neg_formula, merge_literals=False)

        left_sides_formula = left_sides


        preamble_cls = {}
        for p in monitored_vars:
            old_vars = monitored_vars[p]['ports']

            if p not in preamble_cls:
                preamble_cls[p] = {}

            for ov in old_vars:

                if ov not in preamble_cls[p]:
                    preamble_cls[p][ov] = set()

                temp = Equivalence(p.literal, ov.literal, merge_literals=False)
                temp = Globally(temp)
                preamble_cls[p][ov].add(temp)

        for c in counterexamples[1:]:
            new_neg = neg_formula.generate()
            new_neg = LTL_PARSER.parse(new_neg)
            #now the unique names of the original formula are the base_names of the new

            new_vars = dict(new_neg.get_literal_items())

            new_c = c.generate()
            new_c = LTL_PARSER.parse(new_c)

            # LOG.debug(new_c)

            new_c_vars = dict(new_c.get_literal_items())

            for name, var in new_c_vars.items():
                var.merge(new_vars[name])


            new_left = left_sides.generate()
            new_left = LTL_PARSER.parse(new_left)

            new_left_vars = dict(new_left.get_literal_items())

            for name, var in new_left_vars.items():
                var.merge(new_vars[name])

            # LOG.debug(new_vars)
            # LOG.debug(preamble)

            for p in monitored_vars:
                old_vars = monitored_vars[p]['ports']

                if p.unique_name in new_vars:
                    for ov in old_vars:
                        if ov.unique_name in new_vars:
                            temp1 = Equivalence(new_vars[p.unique_name], new_vars[ov.unique_name], merge_literals=False)
                            temp1 = Globally(temp1)
                            preamble_cls[p][ov].add(temp1)

                            # imp = Implication(temp, temp1, merge_literals=False)
                            #
                            # conditions.appe   nd(imp)



            temp = Implication(new_c, new_neg, merge_literals=False)
            formula = Conjunction(formula, temp, merge_literals=False)

            left_sides_formula = Conjunction(left_sides_formula, new_left, merge_literals=False)

            # LOG.debug(temp)
            # LOG.debug(left_sides_formula)

            # if len(conditions) > 0:
            #     cond = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), conditions)
            #     #LOG.debug(cond)
            #     new_neg_formula = Conjunction(new_neg_formula, cond, merge_literals=False)

        init = None
        # LOG.debug(preamble_cls)
        for p_dict in preamble_cls.values():
            p_formulas = []
            for c_set in p_dict.values():
                f = reduce(lambda x,y: Conjunction(x, y, merge_literals=False), c_set)
                p_formulas.append(f)

            f = reduce(lambda x, y: Disjunction(x, y, merge_literals=False), p_formulas)

            if init is None:
                init = f
            else:
                init = Conjunction(init, f, merge_literals=False)

        assert (init is not None)
        # LOG.debug(init)
        temp = Conjunction(init, left_sides_formula, merge_literals=False)
        temp = Conjunction(temp, Negation(all_candidates), merge_literals=False)
        formula = Implication(temp, formula, merge_literals=False)


        # LOG.debug(formula)
        # formula = Implication(new_preamble, new_neg_formula, merge_literals=False)
        return formula


#TODO: case in which preamble is None

def exists_forall_learner(ref_formulas, neg_formula, preamble, left_sides, monitored_variables,
                          input_variables, terminate_evt):
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
    all_cex = None
    cex_list = []
    all_candidates = None


    if preamble is None:
        #no extra connections, we try directly if the composition works

        for ref_formula in ref_formulas:
            # ref_formula = build_formulas_for_other_spec(connected_spec, spec, composition)
            l_passed = verify_tautology(ref_formula, return_trace=False)

            if not l_passed:
                break
        # LOG.debug("no preamble")
        # LOG.debug(l_passed)
        return l_passed, None, None, {}
    else:

        conj_specs = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), ref_formulas)
        # neg_ref = Negation(conj_specs)

        # LOG.debug(preamble)
        # LOG.debug(conj_specs)

        while not l_passed:
            # check again if terminate is set
            if terminate_evt.is_set():
                return False, None, None, None

            # if candidate is None:
            #     # nope, not found
            #     # LOG.debug('nope')
            #     return False, None, None, None
            else:
                # LOG.debug(preamble)
                if len(cex_list) > 0:
                    LOG.debug(len(cex_list))
                    # formula = build_formula_for_multiple_inputs(preamble, all_candidates, neg_formula, left_sides, cex_list, monitored_variables)

                    left = Conjunction(preamble, left_sides, merge_literals=False)
                    left = Conjunction(left, Negation(all_candidates), merge_literals=False)
                    # left = Conjunction(left, all_cex, merge_literals=False)

                    formula = Implication(left, neg_formula, merge_literals=False)

                else:
                    temp = Conjunction(preamble, left_sides, merge_literals=False)
                    formula = Implication(temp, neg_formula, merge_literals=False)



                # LOG.debug(formula.generate())
                l_passed, trace = verify_tautology(formula, return_trace=True)

                # LOG.debug(l_passed)
                # LOG.debug(trace)
                # LOG.debug(l_passed)
                print('.'),
                # LOG.debug(formula.generate())

                    # diff = parse_counterexample(trace, monitored)

                if terminate_evt.is_set():
                    return False, None, None, None

                if l_passed:
                    #if this passes, it means that we are done. This is NOT a solution.
                    # we could find an assignment that makes the formula false,
                    # or the formula is always false for any possible connection
                    # LOG.debug('bad candidate')
                    return False, candidate,preamble, None

                else:
                    #we learn the sequence for the input variables
                    var_assign, ret_assign = trace_analysis(trace, monitored_variables)

                    #build constraints from var assignment
                    v_assign = []

                    # LOG.debug(trace)
                    # # LOG.debug(monitored_variables)
                    # for p in monitored_variables:
                    #     LOG.debug(p.unique_name)
                    # LOG.debug(var_assign)

                    for p in var_assign:
                        for v_p in var_assign[p]:
                            v_assign.append(Globally(Equivalence(p.literal, v_p.literal, merge_literals=False)))
                            break

                    candidate_connection = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), v_assign)

                    # LOG.debug(candidate_connection)

                    # if all_candidates is not None:
                    #     test = Implication(all_candidates, candidate_connection, merge_literals=False)
                    #
                    #     l_passed = verify_tautology(test, return_trace=False)
                    #
                    #     assert not l_passed

                    # if all_candidates is None:
                    #     all_candidates = candidate_connection
                    # else:
                    #     all_candidates = Disjunction(all_candidates, candidate_connection, merge_literals=False)


                    #now check if candidate is a good solution in general:

                    #test for all specs:
                    # for ref_formula in ref_formulas:
                    # if all_cex is not None:
                    #     candidate_connection = Conjunction(candidate_connection, Negation(all_cex), merge_literals=False)
                    for ref_formula in ref_formulas:
                        candidate = Implication(candidate_connection, ref_formula, merge_literals=False)

                        l_passed, trace = verify_tautology(candidate, return_trace=True)

                        if terminate_evt.is_set():
                            return False, None, None, None

                        if not l_passed:
                            break

                    if terminate_evt.is_set():
                        return False, None, None, None
                    # LOG.debug(l_passed)
                    # LOG.debug(trace)
                    # if not l_passed:
                    #     new_preamble = Conjunction(preamble, Negation(candidate_connection), merge_literals=False)
                    # else:
                    #     new_preamble = preamble
                    # new_preamble = preamble


                    var_assign, _ = trace_analysis(trace, monitored_variables)

                    # build constraints from var assignment
                    v_assign = []

                    for p in var_assign:
                        p_opt = []
                        for v_p in var_assign[p]:
                            p_opt.append(Globally(Equivalence(p.literal, v_p.literal, merge_literals=False)))

                        if len(p_opt) > 0:
                            temp = reduce(lambda x, y: Disjunction(x, y, merge_literals=False), p_opt)
                            v_assign.append(temp)

                    if len(v_assign) > 0:
                        candidate = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), v_assign)

                        # LOG.debug(candidate)
                        if all_candidates is None:
                            all_candidates = candidate
                        else:
                            all_candidates = Disjunction(all_candidates, candidate, merge_literals=False)


                    # if l_passed:
                        # LOG.debug('FOUND!')
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

                    if not l_passed:
                        #derive the input sequence anyway, as it can be used for other specs
                        input_formula, i = derive_inputs_from_trace(trace, input_variables)

                        # if len(next_counters) > 0:
                        #     val = next_counters[-1]
                        #     next_counters.append(val + i)
                        # else:
                        #     next_counters.append(i)

                        if input_formula is not None:
                            # LOG.debug(input_formula.generate())

                            #if components are non-deterministic,
                            # it can happen that the same counterexample is shown over and over.
                            # we need to make sure we learn something new.
                            if all_cex is None:
                                all_cex = input_formula
                                cex_list.append(input_formula)
                            else:

                                #next_cex = Disjunction(all_cex, input_formula, merge_literals=False)

                                # check = Implication(input_formula, all_cex, merge_literals=False)
                                # checked = verify_tautology(check, return_trace=False)
                                #
                                # if checked:
                                if False:
                                    LOG.debug('same learned input sequence... done with this candidate')
                                    # LOG.debug('check for non-deterministic solutions')

                                    LOG.debug("wait")

                                    #not a good solution
                                    #return l_passed, None, None, {}
                                else:
                                    LOG.debug('good cex')
                                    all_cex = Disjunction(all_cex, input_formula, merge_literals=False)
                                    cex_list.append(input_formula)
                                    preamble = Conjunction(preamble, input_formula, merge_literals=False)
                        # else:
                        #     new_preamble = preamble
                        else:

                            # LOG.debug('no input formula')
                            return l_passed, None, None, {}

        LOG.debug("FOUND")
        return l_passed, candidate, preamble, ret_assign



    # return (l_passed, trace, checked_variables, monitored, model_map, contracts, composition,
    #         spec_contract, last_iteration)


def derive_inputs_from_trace(trace, input_variables):
    """
    Derives a formula encoding the input sequence used in the trace
    :param trace:
    :param input_variables:
    :return:
    """

    time_sequence = []
    i = -1

    unique_names = {p.unique_name: p for p in input_variables}

    # LOG.debug(trace)
    # LOG.debug(monitored_vars)

    #create structure to record values

    # #process only the first one
    # p = monitored_vars.keys()[0]
    # for p in input_variables:
    #     # LOG.debug(p.base_name)
    #     # LOG.debug(p.unique_name)
    #     c_vars[p.unique_name]= None
    #     var_assign[p] = set()
    #
    #     for v_p in input_variables[p]['ports']:
    #         # LOG.debug(v_p.base_name)
    #         # LOG.debug(v_p.unique_name)
    #         c_vars[v_p.unique_name] = None
    #         var_assign[p].add(v_p)


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
            i = i + 1
            time_sequence.append({})

            # new state, check consistency among vars
            # LOG.debug(c_vars)
            # for p in input_variables:
            #
            #     if i > 0:
            #         time_sequence[i][p.unique_name] = time_sequence[i-1][p.unique_name]
            #     else:
            #         time_sequence[i][p.unique_name] = Constant(0)

            # LOG.debug(diff)


        elif line.startswith('--'):
            # indicates loop in trace, skip line
            pass
        else:
            line_elems = line.split('=')
            line_elems = [l.strip() for l in line_elems]

            # LOG.debug(line_elems)
            # LOG.debug(c_vars)

            if line_elems[0] in unique_names:
                # base_n = monitored_vars[line_elems[0]]

                if line_elems[1] == 'TRUE':
                    val = TrueFormula()
                elif line_elems[1] == 'FALSE':
                    val = FalseFormula()
                else:
                    try:
                        val = int(line_elems[1])
                    except ValueError:
                        val = float(line_elems[1])

                    val = Constant(val)

                time_sequence[i][line_elems[0]] = val


    formula_bits = []
    for i in range(len(time_sequence)):

        inner = []

        for u_name, val in time_sequence[i].items():
            inner.append(Equivalence(unique_names[u_name].literal, val, merge_literals=False))

        if len(inner) > 0:
            inner = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), inner)

            for j in range(i):
                inner = Next(inner)

            formula_bits.append(inner)

    try:
        conj = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), formula_bits)
    except TypeError:
        formula = None
    else:
        # formula = Globally(Eventually(conj))
        formula = conj

    return formula, i

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
                    if v_p in var_assign[p] and c_vars[v_p.unique_name] != p_val and c_vars[v_p.unique_name] is not None:
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
                elif line_elems[1] == 'FALSE':
                    val = False
                else:
                    try:
                        val = int(line_elems[1])
                    except ValueError:
                        val = float(line_elems[1])

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
            break

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