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

    (composition, spec_contract, ref_formulas,
     neg_formula, preamble, left_sides, var_map) = process_model(spec_list, output_port_names,
                                                     model, relevant_contracts, manager)

    input_variables = set([p for p in spec_contract.input_ports_dict.values()])


        # from graphviz_converter import GraphizConverter
        # graphviz_conv = GraphizConverter(connected_spec, composition, contracts)
        # graphviz_conv.generate_graphviz()
        # graphviz_conv.view()

    # else:
    #     #other specs have different unique names
    #     # LOG.debug('here')
    #     ref_formula = build_formulas_for_other_spec(connected_spec, spec, composition)


    #performs first step of learning loo?p
    passed, candidate, new_preamble = exists_forall_learner(composition, spec_contract, spec_list, ref_formulas, neg_formula, preamble, left_sides,
                                                                        var_map, input_variables, terminate_evt)
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


def extract_model_connections(spec_contract, relevant_contracts, library):
    '''
    Extract possible connections form model
    :return:
    '''

    #build dict with ports and possible connections

    var_map = {}

    #let's start with the spec
    for s_port in spec_contract.output_ports_dict.values():
        var_map[s_port] = set()

        for c in relevant_contracts:
            for oport in c.output_ports_dict.values():

                if library.check_connectivity(s_port, oport):
                    var_map[s_port].add(oport)


    #now inter contract connections
    for ci in relevant_contracts:
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



    #LOG.debug(var_map)
    return var_map


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

    # composition mapping to define new names
    # mapping = CompositionMapping(contracts| set([working_spec]))

    #process working specs
    for ws in working_specs.values():
        for port in ws.ports_dict.values():
            name = port.base_name

            spec_contract.connect_to_port(spec_contract.ports_dict[name], port)



    var_map = extract_model_connections(spec_contract, relevant_contracts, library)

    #composition names
    #mappings = {s.unique_name: CompositionMapping(relevant_contracts | {working_specs[s.unique_name]}) for s in spec_list}
    mapping = CompositionMapping(relevant_contracts | {spec_contract})
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


    root = relevant_contracts.pop()
    composition = root.compose(relevant_contracts, composition_mapping=mapping)
    relevant_contracts.add(root)

    #TODO: can we simplify this?
    ref_formulas = [build_formulas_for_other_spec(s, composition) for s in
                    working_specs.values()]
    # ref_formula = build_formula_for_all_specs(spec_contract, spec_list, composition)
    neg_formula = build_neg_formula_for_all_specs(working_specs.values(), composition)

    # neg_formula = Negation(reduce(lambda x, y: Conjunction(x, y, merge_literals=False), ref_formulas))

    formulas = []
    for port in var_map:
        p_map = []

        for p in var_map[port]:
            inner = Globally(Equivalence(port.literal, p.literal, merge_literals=False))
            p_map.append(inner)

        if len(p_map) > 0:
            formula = reduce((lambda x, y: Disjunction(x, y, merge_literals=False)), p_map)
            formulas.append(formula)


    left_sides = TrueFormula()
    preamble = TrueFormula()

    if len(formulas) > 0:

        preamble = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), formulas)


        left_sides = Conjunction(left_sides, composition.guarantee_formula, merge_literals=False)

        for s in working_specs.values():
            left_sides = Conjunction(left_sides, s.assume_formula, merge_literals=False)
            break


    # #name map
    # var_name_map = {}
    # for c in [spec_contract] + relevant_contracts:
    #     for p in c.ports_dict.values():
    #         var_name_map[p.unique_name] = p

    return composition, spec_contract, ref_formulas, neg_formula, preamble, left_sides, var_map




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


#TODO: case in which preamble is None

def get_all_candidates(trace, var_map, current_pool=None):
    ''' return a formula indicating all candidates from a trace'''
    var_assign = trace_analysis(trace, var_map)

    v_assign = []

    num = 1

    for p in var_assign:
        p_opt = []

        if current_pool is not None and p not in current_pool:
            continue

        num = num * len(var_assign[p])
        for v_p in var_assign[p]:
            if current_pool is not None and v_p not in current_pool[p]:
                #remove
                num = num / len(var_assign[p])
                continue
            p_opt.append(Globally(Equivalence(p.literal, v_p.literal, merge_literals=False)))

        if len(p_opt) > 0:
            temp = reduce(lambda x, y: Disjunction(x, y, merge_literals=False), p_opt)
            v_assign.append(temp)

    if len(v_assign) > 0:
        candidate_connection = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), v_assign)

    return candidate_connection, num

def exists_forall_learner(composition, spec_contract, spec_list, ref_formulas, neg_formula, preamble, left_sides, var_map, input_variables, terminate_evt):
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
    all_cex = TrueFormula()
    cex_list = []
    tested_candidates = None
    current_cex = None
    all_candidates = None


    total = 1
    for p in var_map:
        total *= len(var_map[p])

    LOG.debug("TOTAL: %d candidates" % total)
    num_left = total

    all_spec_assumptions = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), [x.assume_formula for x in spec_list])
    c_assumptions = composition.assume_formula

    all_assumptions = Conjunction(all_spec_assumptions, c_assumptions, merge_literals=False)

    if preamble is None:
        #no extra connections, we try directly if the composition works

        for ref_formula in ref_formulas:
            # ref_formula = build_formulas_for_other_spec(connected_spec, spec, composition)
            l_passed = verify_tautology(ref_formula, return_trace=False)

            if not l_passed:
                break
        LOG.debug("no preamble")
        LOG.debug(l_passed)
        return l_passed, None, None
    else:

        conj_specs = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), ref_formulas)
        # neg_ref = Negation(conj_specs)

        # LOG.debug(preamble)
        # LOG.debug(conj_specs)


        while True:
            if terminate_evt.is_set():
                return False, None, None

            left = Conjunction(preamble, left_sides, merge_literals=False)
            if tested_candidates is not None:
                left = Conjunction(left, Negation(tested_candidates), merge_literals=False)

            if current_cex is not None:
                #LOG.debug(current_cex)
                left = Conjunction(left, current_cex, merge_literals=False)

            l_passed, trace = verify_candidate(left, neg_formula)

            print('.'),

            if l_passed:
                #if this passes, it means that we are done. This is NOT a solution.
                # we could find an assignment that makes the formula false,
                # or the formula is always false for any possible connection
                LOG.debug('bad candidate')
                return False, candidate,preamble

            else:
                candidate_connection, _ = get_all_candidates(trace, var_map)

                left = candidate_connection

                # left = Conjunction(candidate_connection, left_sides, merge_literals=False)
                # left = Conjunction(candidate_connection, all_assumptions, merge_literals=False)
                # left = Conjunction(left, spec_contract.guarantee_formula, merge_literals=False)
                # left = Conjunction(left, composition.guarantee_formula, merge_literals=False)
                if tested_candidates is not None:
                    left = Conjunction(left, Negation(tested_candidates), merge_literals=False)

                if current_cex is not None:
                    left = Conjunction(left, current_cex, merge_literals=False)

                # check for termination
                if terminate_evt.is_set():
                    return False, None, None
                l_passed, trace = verify_candidate(left, conj_specs)


                tested_c, num = get_all_candidates(trace, var_map)
                #LOG.debug('remove %d candidates' % num)
                #num_left = num_left - num
                #LOG.debug('Candidates left = %d ' % num_left)
                #assert num_left >= 0

                # update tested candidates
                if tested_candidates is None:
                    tested_candidates = tested_c
                else:
                    tested_candidates = Disjunction(tested_candidates, tested_c, merge_literals=False)


                if l_passed:
                    #make sure it's right verify if it's a global solution

                    # check for termination
                    if terminate_evt.is_set():
                        return False, None, None
                    LOG.debug("GOOD. let's double check")
                    local_pass, _ = verify_candidate(candidate_connection, conj_specs)

                    if local_pass:
                        #success
                        candidate = candidate_connection
                        break
                    else:
                        #we need a new counterexample, but now tested_candidates will remove this set of solutions
                        LOG.debug("nah")
                        LOG.debug('reset CEX')
                        current_cex = None
                else:
                    #update counterexample
                    LOG.debug('update CEX')
                    LOG.debug(current_cex)
                    # LOG.debug(trace)
                    input_formula, _ = derive_inputs_from_trace(trace, input_variables)
                    assert input_formula is not None
                    LOG.debug(input_formula)

                    # if current_cex is not None:
                    #     check = Implication(input_formula, current_cex, merge_literals=False)
                    #     checked = verify_tautology(check, return_trace=False)
                    #
                    #     assert checked
                    current_cex = input_formula




        # while not l_passed:
        #     # check again if terminate is set
        #     if terminate_evt.is_set():
        #         return False, None, None, None
        #
        #     # if candidate is None:
        #     #     # nope, not found
        #     #     # LOG.debug('nope')
        #     #     return False, None, None, None
        #     else:
        #         # LOG.debug(preamble)
        #         # LOG.debug(left_sides)
        #
        #         left = Conjunction(preamble, left_sides, merge_literals=False)
        #         if all_candidates is not None:
        #             left = Conjunction(left, Negation(all_candidates), merge_literals=False)
        #
        #         if current_cex is not None:
        #             LOG.debug(current_cex)
        #             left = Conjunction(left, current_cex, merge_literals=False)
        #
        #
        #         l_passed, trace = verify_candidate(left, neg_formula)
        #
        #         LOG.debug(l_passed)
        #         #LOG.debug(trace)
        #         print('.'),
        #         # LOG.debug(formula.generate())
        #
        #             # diff = parse_counterexample(trace, monitored)
        #
        #         if terminate_evt.is_set():
        #             return False, None, None, None
        #
        #         if l_passed:
        #             #if this passes, it means that we are done. This is NOT a solution.
        #             # we could find an assignment that makes the formula false,
        #             # or the formula is always false for any possible connection
        #             # LOG.debug('bad candidate')
        #             return False, candidate,preamble, None
        #
        #
        #             # left = Conjunction(preamble, left_sides, merge_literals=False)
        #             # if all_candidates is not None:
        #             #     left = Conjunction(left, Negation(all_candidates), merge_literals=False)
        #             #
        #             # l_passed, trace = verify_candidate(left, neg_formula)
        #             #
        #             # if l_passed:
        #             #     #if this passes, it means that we are done. This is NOT a solution.
        #             #     # we could find an assignment that makes the formula false,
        #             #     # or the formula is always false for any possible connection
        #             #     # LOG.debug('bad candidate')
        #             #     return False, candidate,preamble, None
        #             # else:
        #             #     LOG.debug('reset CEX')
        #             #     current_cex = None
        #
        #
        #         # LOG.debug(candidate_connection)
        #         #
        #         # if all_candidates is None:
        #         #     all_candidates = candidate_connection
        #         # else:
        #         #     all_candidates = Disjunction(all_candidates, candidate_connection, merge_literals=False)
        #         #
        #         #     continue
        #
        #         all_local_candidates = None
        #         #current_pool = None
        #         while True:
        #
        #             candidate_connection = get_all_candidates(trace, var_map)
        #             vanilla_candidate = candidate_connection
        #
        #             if all_local_candidates is not None:
        #                 check = Implication(candidate_connection, all_local_candidates, merge_literals=False)
        #                 checked = verify_tautology(check, return_trace=False)
        #
        #                 try:
        #                     assert checked
        #                 except AssertionError as e:
        #                     #print e
        #                     LOG.debug(l_passed)
        #                     LOG.debug(trace)
        #                     LOG.debug(candidate_connection)
        #                     LOG.debug(all_local_candidates)
        #                     raise
        #
        #                 all_local_candidates = Conjunction(all_local_candidates, Negation(candidate_connection),
        #                                                    merge_literals=False)
        #             else:
        #                 all_local_candidates = candidate_connection
        #
        #
        #             if all_candidates is None:
        #                 all_candidates = vanilla_candidate
        #             else:
        #                 all_candidates = Disjunction(all_candidates, vanilla_candidate, merge_literals=False)
        #
        #
        #             if current_cex is not None:
        #                 candidate = Conjunction(all_local_candidates, current_cex, merge_literals=False)
        #             else:
        #                 candidate = all_local_candidates
        #
        #
        #             l_passed, trace = verify_candidate(candidate, conj_specs)
        #
        #
        #             if terminate_evt.is_set():
        #                 return False, None, None, None
        #
        #
        #             if l_passed:
        #                 # make sure it passes even without cex
        #                 # LOG.debug(current_cex)
        #
        #                 l_passed, trace = verify_candidate(vanilla_candidate, conj_specs)
        #                 if not l_passed:
        #                     # we cannot go further with these candidates and cex
        #                     LOG.debug('BREAK')
        #                     break
        #                 else:
        #                     # LOG.debug('no input formula')
        #                     return l_passed, None, None, {}
        #             else:
        #                 #derive the input sequence anyway, as it can be used for other specs
        #                 input_formula, i = derive_inputs_from_trace(trace, input_variables)
        #
        #                 assert input_formula is not None
        #
        #                 #LOG.debug(input_formula)
        #
        #                 #if components are non-deterministic,
        #                 # it can happen that the same counterexample is shown over and over.
        #                 # we need to make sure we learn something new.
        #                 if current_cex is None:
        #                     current_cex = input_formula
        #                 else:
        #
        #                     # check = Implication(input_formula, current_cex, merge_literals=False)
        #                     # checked = verify_tautology(check, return_trace=False)
        #                     #
        #                     # assert checked
        #
        #                     current_cex = input_formula
        #
        #                 #loop to reduce current candidate
        #
        #                 #loop_candidate = get_all_candidates(trace, var_map)
        #
        #                 left = Conjunction(vanilla_candidate, left_sides, merge_literals=False)
        #                 if all_candidates is not None:
        #                     left = Conjunction(left, Negation(all_candidates), merge_literals=False)
        #
        #
        #                 #all_local_candidates = Conjunction(all_local_candidates, Negation(loop_candidate),
        #                  #                                  merge_literals=False)
        #
        #
        #                 if current_cex is not None:
        #                     left = Conjunction(left, current_cex, merge_literals=False)
        #
        #                 l_passed, ctrace = verify_candidate(left, neg_formula)
        #
        #                 if l_passed:
        #                     all_candidates = Disjunction(all_candidates, vanilla_candidate, merge_literals=False)
        #                     LOG.debug('down BREAK')
        #                     l_passed = False
        #                     break



        LOG.debug("FOUND")
        LOG.debug(l_passed)
        LOG.debug(candidate)
        l_passed, trace = verify_candidate(candidate, conj_specs)
        LOG.debug(l_passed)

        return l_passed, candidate, preamble



    # return (l_passed, trace, checked_variables, monitored, model_map, contracts, composition,
    #         spec_contract, last_iteration)


def verify_candidate(candidate, spec):
    '''verify whether a candidate is a good one'''

    _candidate = Implication(candidate, spec, merge_literals=False)

    l_passed, trace = verify_tautology(_candidate, return_trace=True)

    return l_passed, trace

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
    pre_trace = True

    for line in lines:
        line = line.strip()

        # LOG.debug(line)

        if not pre_trace:
            if not line.startswith('-- Trace was successfully completed.'):
                continue
            else:
                pre_trace = True
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

def trace_analysis(trace, var_map):
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
    for p in var_map:
        # LOG.debug(p.base_name)
        # LOG.debug(p.unique_name)
        c_vars[p.unique_name]= None
        var_assign[p] = set()

        for v_p in var_map[p]:
            # LOG.debug(v_p.base_name)
            # LOG.debug(v_p.unique_name)
            c_vars[v_p.unique_name] = None
            var_assign[p].add(v_p)


    # LOG.debug(c_vars)
    lines = trace.split('\n')

    after_preamble = False
    pre_trace = True

    #seen = {p_name for p_name in c_vars}

    for line in lines:
        line = line.strip()
        #
        # LOG.debug(line)
        # LOG.debug(seen)
        if not pre_trace:
            if not line.startswith('-- Trace was successfully completed.'):
                continue
            else:
                pre_trace = True

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
            for p in var_map:
                if p in var_assign:
                    p_val = c_vars[p.unique_name]

                    for v_p in var_map[p]:
                        # LOG.debug(v_p.unique_name)
                        # LOG.debug(seen)
                        # LOG.debug(var_assign[p])
                        if (v_p in var_assign[p] and c_vars[v_p.unique_name] != p_val
                            and c_vars[v_p.unique_name] is not None):
                            # LOG.debug('remove')
                            # LOG.debug(p.unique_name)
                            # LOG.debug(p_val)
                            # LOG.debug(v_p.unique_name)
                            # LOG.debug(c_vars[v_p.unique_name])
                            var_assign[p].remove(v_p)

            # LOG.debug(diff)

            # #reset
            # seen = set()

        elif line.startswith('--'):
            # indicates loop in trace, skip line
            pass
        else:
            line_elems = line.split('=')
            line_elems = [l.strip() for l in line_elems]

            # LOG.debug(line_elems)
            # LOG.debug(c_vars)

            if line_elems[0] in c_vars:
                # seen.add(line_elems[0])
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


    # #return assignement
    # ret_assign = {}
    #
    # for p in var_assign:
    #     orig_level, orig_port = monitored_vars[p]['orig']
    #     ret_assign[(orig_level, orig_port)] = set()
    #
    #     for v in var_assign[p]:
    #         origv_level, origv_port = monitored_vars[p]['ports'][v]
    #         ret_assign[(orig_level, orig_port)].add((origv_level, origv_port))
    #         break

    return var_assign


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