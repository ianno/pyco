'''
This module includes the functions necessary to decompose the specification list
according to their outputs.

Author: Antonio Iannopollo
'''

from pyco import LOG
from pyco.contract import CompositionMapping
from pycolite.formula import Globally, Equivalence, Disjunction, Implication, Negation, Conjunction, TrueFormula
from pycolite.nuxmv import NuxmvRefinementStrategy, verify_tautology
from multiprocessing import Process, Queue, Semaphore

MAX_PROCESSES = 10


class OutputProcessor(Process):

    def __init__(self, pivot_name, spec_list, res_queue, semaphore):

        self.pivot_name = pivot_name
        self.spec_list = spec_list
        self.res_queue = res_queue
        self.semaphore = semaphore

        super(OutputProcessor, self).__init__()

    def run(self):
        '''
        process one output at a time
        :return:
        '''
        print('\tprocessing port %s' % self.pivot_name)

        for spec in self.spec_list:

            # build composition
            w_spec = spec.copy()
            w_spec1 = spec.copy()
            w_spec2 = spec.copy()

            mapping = CompositionMapping([w_spec1, w_spec2])

            # connect pivot output port
            w_spec.connect_to_port(w_spec.output_ports_dict[self.pivot_name],
                                   w_spec1.output_ports_dict[self.pivot_name])

            # connect inputs
            for name, in_port in w_spec.input_ports_dict.items():
                w_spec.connect_to_port(in_port, w_spec1.input_ports_dict[name])
                w_spec.connect_to_port(in_port, w_spec2.input_ports_dict[name])

                # # add explicit naming
                # mapping.add(w_spec1.input_ports_dict[name],
                #             '1_' + name)
                # mapping.add(w_spec2.input_ports_dict[name],
                #             '2_' + name)

            # connect remaining outputs
            for name, out_port in w_spec.output_ports_dict.items():
                # add explicit naming
                mapping.add(w_spec1.output_ports_dict[name],
                            '1_' + name)
                mapping.add(w_spec2.output_ports_dict[name],
                            '2_' + name)

                if name != self.pivot_name:
                    w_spec.connect_to_port(out_port, w_spec2.output_ports_dict[name])

            # compose
            composition = w_spec1.compose([w_spec2], composition_mapping=mapping)

            passed = composition.is_refinement(w_spec)

            if passed is False:
                break

        self.res_queue.put((self.pivot_name, passed))
        self.semaphore.release()
        return

class MultipleOutputProcessor(Process):

    def __init__(self, init_cluster, spec_list, res_queue, semaphore):

        self.init_cluster = init_cluster
        self.spec_list = spec_list
        self.res_queue = res_queue
        self.semaphore = semaphore

        super(MultipleOutputProcessor, self).__init__()

    def run(self):
        '''
        process one output at a time
        :return:
        '''
        print('\tmultiple output clusters, processing port %s' % ', '.join(self.init_cluster))

        # LOG.debug(pivot_name)
        cluster = {x for x in self.init_cluster}
        done = {x for x in self.init_cluster}
        # done.add(self.pivot_name)

        while True:
            passed = True

            for spec in self.spec_list:

                unknowns = set(spec.output_ports_dict.keys()) - done
                # LOG.debug(unknowns)
                # LOG.debug(cluster)

                if len(unknowns) == 0:
                    # we are done
                    break
                # elif len(unknowns) == 1:
                #     # last one must go with the previous one
                #     elem = unknowns.pop()
                #     cluster.add(elem)
                #     done.add(elem)
                else:

                    # build composition
                    w_spec = spec.copy()
                    w_spec1 = spec.copy()
                    w_spec2 = spec.copy()

                    mapping = CompositionMapping([w_spec1, w_spec2])

                    # connect pivot output port
                    for name in cluster:
                        w_spec.connect_to_port(w_spec.output_ports_dict[name],
                                               w_spec1.output_ports_dict[name])

                    # connect inputs
                    for name, in_port in w_spec.input_ports_dict.items():
                        w_spec.connect_to_port(in_port, w_spec1.input_ports_dict[name])
                        w_spec.connect_to_port(in_port, w_spec2.input_ports_dict[name])

                    # connect remaining outputs
                    for name, out_port in w_spec.output_ports_dict.items():
                        # add explicit naming
                        mapping.add(w_spec1.output_ports_dict[name],
                                    '1_' + name)
                        mapping.add(w_spec2.output_ports_dict[name],
                                    '2_' + name)

                        if name not in cluster:
                            w_spec.connect_to_port(out_port, w_spec2.output_ports_dict[name])

                    # compose
                    composition = w_spec1.compose([w_spec2], composition_mapping=mapping)

                    # LOG.debug(composition)
                    # LOG.debug(w_spec1)
                    # LOG.debug(w_spec2)

                    # add conditionals
                    # (G(a1=a2 & b1!=b2 &...) | G(b1=b2 & a1!=a2 & ...)...) -> Spec ref. formula


                    # left_formula = []
                    # for pivot in unknowns:
                    #     formula_l = [TrueFormula()]
                    #
                    #     # formula_l.append(Negation(Globally(Equivalence(w_spec1.ports_dict[pivot].literal,
                    #     #                                                w_spec2.ports_dict[pivot].literal,
                    #     #                                                merge_literals=False)
                    #     #                                    )
                    #     #                           )
                    #     #                  )
                    #
                    #     for name in unknowns - {pivot}:
                    #         formula_l.append(Globally(Equivalence(w_spec1.ports_dict[name].literal,
                    #                                               w_spec2.ports_dict[name].literal,
                    #                                               merge_literals=False)
                    #                                   )
                    #                          )
                    #
                    #     formula = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), formula_l)
                    #
                    #     left_formula.append(formula)
                    #
                    # formula = reduce(lambda x, y: Disjunction(x, y, merge_literals=False), left_formula)

                    # get refinement formula
                    verifier = NuxmvRefinementStrategy(composition)

                    ref_formula = verifier.get_refinement_formula(w_spec)

                    # formula = Implication(formula, ref_formula, merge_literals=False)
                    # l_passed, trace = verify_tautology(formula, return_trace=True)

                    l_passed, trace = verify_tautology(ref_formula, return_trace=True)

                    # LOG.debug(l_passed)
                    # LOG.debug(formula.generate())

                    if not l_passed:

                        # build monitored vars dict
                        monitored = {}

                        for name in unknowns:
                            monitored[composition.ports_dict['1_' + name].unique_name] = name
                            monitored[w_spec.ports_dict[name].unique_name] = name

                        # LOG.debug(composition)
                        # LOG.debug(cluster)
                        # LOG.debug(unknowns)
                        # LOG.debug(done)
                        # LOG.debug(monitored)
                        # LOG.debug(trace)
                        diff = parse_counterexample(trace, monitored)
                        # LOG.debug(diff)

                        assert len(diff) > 0
                        # LOG.debug(diff)
                        for elem in diff:
                            cluster.add(elem)
                            done.add(elem)

                    passed &= l_passed

            # go out of the while loop
            if passed:
                break

        assert len(cluster) >= 1

        for pivot in self.init_cluster:
            self.res_queue.put((pivot, frozenset(cluster)))
        self.semaphore.release()
        return

def find_useless_inputs(contract, independent_outputs):
    '''
    identifies what inputs do not have any impact on the outputs.

    :param contract:
    :return:
    '''

    useless = set()

    for pivot in contract.input_ports_dict:

        alpha = contract.copy()
        duplicate = contract.copy()


        #add constraints which forces all the other ports to be the same?
        bits = [TrueFormula()]
        for name in independent_outputs:
            p1 = alpha.output_ports_dict[name]
            p2 = duplicate.output_ports_dict[name]

            alpha.connect_to_port(p1, p2)

        # connect all outputs
        for name, out_port in alpha.output_ports_dict.items():
            if name not in independent_outputs:
                bits.append(Globally(Equivalence(out_port.literal, duplicate.output_ports_dict[name].literal, merge_literals=False)))

        form = reduce(lambda x,y: Conjunction(x,y,merge_literals=False), bits)
        print(form)

        #connect all inputs - pivot
        for name, in_port in alpha.input_ports_dict.items():
            if name != pivot:
                alpha.connect_to_port(in_port, duplicate.input_ports_dict[name])


        verifier = NuxmvRefinementStrategy(duplicate)

        ref_formula = verifier.get_refinement_formula(alpha)

        formula = Implication(form, ref_formula, merge_literals=False)

        l_passed, trace = verify_tautology(formula, return_trace=True)

        if l_passed:
            useless.add(pivot)


    return useless



def decompose_spec(spec_list, library=None):
    '''
    decompose specification in clusters of outputs
    :param spec_list:
    :return:
    '''

    spec_root = spec_list[0]

    spec_outs_dict = spec_root.output_ports_dict

    clusters = []

    unclustered = set(spec_outs_dict.keys())
    done = set()

    #preprocess:
    # find ports which behave exactly the same
    init_clusters = []
    done = set()
    for pivot_name in unclustered:

        if pivot_name not in done:
            cluster = {pivot_name}
            done.add(pivot_name)


            # for other_name in (unclustered - set([pivot_name])):
            #
            #     if library is None or library.check_connectivity(spec_root.ports_dict[pivot_name],
            #                                   spec_root.ports_dict[other_name]):
            #
            #         for spec in spec_list:
            #             w_spec = spec.copy()
            #
            #             formula_r = Globally(Equivalence(w_spec.ports_dict[pivot_name].literal,
            #                                                               w_spec.ports_dict[other_name].literal,
            #                                                               merge_literals=False))
            #
            #             guarantees = w_spec.guarantee_formula
            #
            #             formula = Implication(guarantees, formula_r, merge_literals=False)
            #
            #             l_passed = verify_tautology(formula, return_trace=False)
            #
            #             if not l_passed:
            #                 break
            #
            #
            #         if l_passed:
            #             cluster.add(other_name)
            #             done.add(other_name)

            init_clusters.append(cluster)

    #done

    # first FAST pass, try to take out as many single ports as possible
    res_queue = Queue()
    pool = []
    semaphore = Semaphore(MAX_PROCESSES)
    #
    # for pivot_name in spec_outs_dict:
    #     semaphore.acquire()
    #     proc = OutputProcessor(pivot_name, spec_list, res_queue, semaphore)
    #     proc.start()
    #     pool.append(proc)
    #
    # for p in pool:
    #     p.join()
    #
    # #everyone is done now
    # while not res_queue.empty():
    #     res = res_queue.get_nowait()
    #     if res[1] is True:
    #         clusters.append(set([res[0]]))
    #     else:
    #         unclustered.add(res[0])


    # for pivot_name in spec_outs_dict:
    #
    #     print('\tprocessing port %s' % pivot_name)
    #
    #     passed = True
    #     for spec in spec_list:
    #
    #         # build composition
    #         w_spec = spec.copy()
    #         w_spec1 = spec.copy()
    #         w_spec2 = spec.copy()
    #
    #         mapping = CompositionMapping([w_spec1, w_spec2])
    #
    #         # connect pivot output port
    #         w_spec.connect_to_port(w_spec.output_ports_dict[pivot_name],
    #                                w_spec1.output_ports_dict[pivot_name])
    #
    #         # connect inputs
    #         for name, in_port in w_spec.input_ports_dict.items():
    #             w_spec.connect_to_port(in_port, w_spec1.input_ports_dict[name])
    #             w_spec.connect_to_port(in_port, w_spec2.input_ports_dict[name])
    #
    #             # # add explicit naming
    #             # mapping.add(w_spec1.input_ports_dict[name],
    #             #             '1_' + name)
    #             # mapping.add(w_spec2.input_ports_dict[name],
    #             #             '2_' + name)
    #
    #         # connect remaining outputs
    #         for name, out_port in w_spec.output_ports_dict.items():
    #             # add explicit naming
    #             mapping.add(w_spec1.output_ports_dict[name],
    #                         '1_' + name)
    #             mapping.add(w_spec2.output_ports_dict[name],
    #                         '2_' + name)
    #
    #             if name != pivot_name:
    #                 w_spec.connect_to_port(out_port, w_spec2.output_ports_dict[name])
    #
    #         # compose
    #         composition = w_spec1.compose([w_spec2], composition_mapping=mapping)
    #
    #         passed &= composition.is_refinement(w_spec)
    #
    #         if not passed:
    #             break
    #
    #     if passed:
    #         clusters.append(set([pivot_name]))
    #     else:
    #         unclustered.add(pivot_name)

    # now process remaining unclustered elements, a bit slower.
    # we need to give a special input to the model checker,
    # to let it suggest what are related outputs
    for init in init_clusters:

        semaphore.acquire()
        proc = MultipleOutputProcessor(init, spec_list, res_queue, semaphore)
        proc.start()
        pool.append(proc)

    for p in pool:
        p.join()

        # everyone is done now
    while not res_queue.empty():
        (name, cluster) = res_queue.get_nowait()
        # LOG.debug(cluster)
        clusters.append(set(cluster))



        # # LOG.debug(pivot_name)
        # cluster = set([pivot_name])
        # done = set()
        # done.add(pivot_name)
        #
        # while True:
        #     passed = True
        #
        #     for spec in spec_list:
        #
        #         unknowns = set(spec_outs_dict.keys()) - done
        #         # LOG.debug(unknowns)
        #         # LOG.debug(cluster)
        #
        #         if len(unknowns) == 0:
        #             # we are done
        #             break
        #         # elif len(unknowns) == 1:
        #         #     # last one must go with the previous one
        #         #     elem = unknowns.pop()
        #         #     cluster.add(elem)
        #         #     done.add(elem)
        #         else:
        #
        #             # build composition
        #             w_spec = spec.copy()
        #             w_spec1 = spec.copy()
        #             w_spec2 = spec.copy()
        #
        #             mapping = CompositionMapping([w_spec1, w_spec2])
        #
        #             # connect pivot output port
        #             for name in cluster:
        #                 w_spec.connect_to_port(w_spec.output_ports_dict[name],
        #                                        w_spec1.output_ports_dict[name])
        #
        #             # connect inputs
        #             for name, in_port in w_spec.input_ports_dict.items():
        #                 w_spec.connect_to_port(in_port, w_spec1.input_ports_dict[name])
        #                 w_spec.connect_to_port(in_port, w_spec2.input_ports_dict[name])
        #
        #             # connect remaining outputs
        #             for name, out_port in w_spec.output_ports_dict.items():
        #                 # add explicit naming
        #                 mapping.add(w_spec1.output_ports_dict[name],
        #                             '1_' + name)
        #                 mapping.add(w_spec2.output_ports_dict[name],
        #                             '2_' + name)
        #
        #                 if name not in cluster:
        #                     w_spec.connect_to_port(out_port, w_spec2.output_ports_dict[name])
        #
        #             # compose
        #             composition = w_spec1.compose([w_spec2], composition_mapping=mapping)
        #
        #             # LOG.debug(composition)
        #             # LOG.debug(w_spec1)
        #             # LOG.debug(w_spec2)
        #
        #             # add conditionals
        #             # (G(a1=a2 & b1!=b2 &...) | G(b1=b2 & a1!=a2 & ...)...) -> Spec ref. formula
        #
        #
        #             left_formula = []
        #             for pivot in unknowns:
        #                 formula_l = []
        #
        #                 formula_l.append(Negation(Globally(Equivalence(w_spec1.ports_dict[pivot].literal,
        #                                                             w_spec2.ports_dict[pivot].literal,
        #                                                             merge_literals=False)
        #                                                    )
        #                                           )
        #                                  )
        #
        #                 for name in unknowns - {pivot}:
        #                     formula_l.append(Globally(Equivalence(w_spec1.ports_dict[name].literal,
        #                                                           w_spec2.ports_dict[name].literal,
        #                                                           merge_literals=False)
        #                                                   )
        #                                      )
        #
        #                 formula = reduce(lambda x, y: Conjunction(x, y, merge_literals=False), formula_l)
        #
        #                 left_formula.append(formula)
        #
        #             formula = reduce(lambda x, y: Disjunction(x, y, merge_literals=False), left_formula)
        #
        #             # get refinement formula
        #             verifier = NuxmvRefinementStrategy(composition)
        #
        #             ref_formula = verifier.get_refinement_formula(w_spec)
        #
        #             formula = Implication(formula, ref_formula, merge_literals=False)
        #
        #             l_passed, trace = verify_tautology(formula, return_trace=True)
        #
        #             # LOG.debug(l_passed)
        #             # LOG.debug(formula.generate())
        #
        #             if not l_passed:
        #
        #                 #build monitored vars dict
        #                 monitored = {}
        #
        #                 for name in unknowns:
        #                     monitored[composition.ports_dict['1_' + name].unique_name] = name
        #                     monitored[w_spec.ports_dict[name].unique_name] = name
        #
        #                 # LOG.debug(composition)
        #                 # LOG.debug(cluster)
        #                 # LOG.debug(unknowns)
        #                 # LOG.debug(done)
        #                 # LOG.debug(monitored)
        #                 # LOG.debug(trace)
        #                 diff = parse_counterexample(trace, monitored)
        #
        #                 assert len(diff) > 0
        #                 LOG.debug(diff)
        #                 for elem in diff:
        #                     cluster.add(elem)
        #                     done.add(elem)
        #
        #             passed &= l_passed
        #
        #     #go out of the while loop
        #     if passed:
        #         break
        #
        # assert len(cluster) > 1
        #
        # # LOG.debug(cluster)
        # clusters.append(cluster)

    assert set([x for cluster in clusters for x in cluster]).issuperset(unclustered)

    #postprocessing, merge clusters with elements in common


    mods = True
    while mods:
        mods = False
        for i in range(len(clusters)):
            cl = clusters[i]
            for j in range(len(clusters)):
                if i != j:
                    ocl = clusters[j]
                    if not cl.isdisjoint(ocl):
                        mods = True
                        clusters[i] = cl | ocl
                        cl = clusters[i]
                        clusters[j] = set([])
    #filter
    clusters = [x for x in clusters if len(x) > 0]

    LOG.debug(clusters)

    # #test useless inputs:
    # for c in clusters:
    #     useless = find_useless_inputs(spec_list[0], c)
    #
    #     print("relevant inputs for ")
    #     print(c)
    #     print(set(spec_list[0].input_ports_dict.keys()) - useless)

    # assert False
    # LOG.debug(unclustered)
    return clusters


def parse_counterexample(ctx_str, monitored_vars):
    '''
    parse the counterexample trace and return the list of vars which are changing
    :param ctx_str:
    :para
    m monitored_vars: needs to be a dict {unique_name: base_name, ...}
    :return:
    '''
    diff = set()
    c_vars = {name: {} for name in monitored_vars.values()}

    for u_name, b_name in monitored_vars.items():
        c_vars[b_name][u_name] = None


    lines = ctx_str.split('\n')

    after_preamble = False

    for line in lines:
        line = line.strip()

        #LOG.debug(line)

        if not after_preamble:
            if not line.startswith('->'):
                continue
            else:
                after_preamble = True
                # LOG.debug('after preamble')

        #done with the preamble
        #analyze state by state
        if line.startswith('->'):
            #new state, check consistency among vars
            # LOG.debug(c_vars)
            for b_name, pair in c_vars.items():
                pair_v = pair.values()
                if not pair_v[0] == pair_v[1]:
                    diff.add(b_name)

        elif line.startswith('--'):
            # indicates loop in trace, skip line
            pass
        else:
            line_elems = line.split('=')
            line_elems = [l.strip() for l in line_elems]

            # LOG.debug(line_elems)
            # LOG.debug(c_vars)

            if line_elems[0] in monitored_vars:
                base_n = monitored_vars[line_elems[0]]

                if line_elems[1] == 'TRUE':
                    val = True
                elif line_elems[1] == 'FALSE':
                    val = False
                else:
                    val = int(line_elems[1])

                c_vars[base_n][line_elems[0]] = val

    return diff





STR = """
*** This is nuXmv 1.0.1 (compiled on Mon Nov 17 17:49:50 2014)
*** Copyright (c) 2014, Fondazione Bruno Kessler

*** For more information on nuXmv see https://nuxmv.fbk.eu
*** or email to <nuxmv@list.fbk.eu>.
*** Please report bugs at https://nuxmv.fbk.eu/bugs
*** (click on "Login Anonymously" to access)
*** Alternatively write to <nuxmv@list.fbk.eu>.

*** This version of nuXmv is linked to NuSMV 2.5.trunk.
*** For more information on NuSMV see <http://nusmv.fbk.eu>
*** or email to <nusmv-users@list.fbk.eu>.
*** Copyright (C) 2010-2014, Fondazione Bruno Kessler

*** This version of nuXmv is linked to the CUDD library version 2.4.1
*** Copyright (c) 1995-2004, Regents of the University of Colorado

*** This version of nuXmv is linked to the MiniSat SAT solver.
*** See http://minisat.se/MiniSat.html
*** Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
*** Copyright (c) 2007-2010, Niklas Sorensson

*** This version of nuXmv is linked to MathSAT
*** Copyright (C) 2014 by Fondazione Bruno Kessler
*** Copyright (C) 2014 by University of Trento
*** See http://mathsat.fbk.eu

-- specification ((( G c2_17_376 = c2_17_377 |  G c6_0_376 = c6_0_377) |  G c5_0_376 = c5_0_377) -> ((TRUE -> ((TRUE & TRUE) | !((!TRUE | (!((c5_0_377 & c6_0_377) & c3_10_754) & !(c2_17_377 & c3_10_754))) & (!TRUE | (!((c5_0_376 & c6_0_376) & c3_10_752) & !(c2_17_376 & c3_10_752)))))) & (((!TRUE | (!((c5_0_377 & c6_0_377) & c3_10_754) & !(c2_17_377 & c3_10_754))) & (!TRUE | (!((c5_0_376 & c6_0_376) & c3_10_752) & !(c2_17_376 & c3_10_752)))) -> (!TRUE | (!((c5_0_377 & c6_0_377) & c3_10_752) & !(c2_17_377 & c3_10_752))))))  is false
-- as demonstrated by the following execution sequence
Trace Description: LTL Counterexample
Trace Type: Counterexample
  -> State: 1.1 <-
    c3_10_754 = FALSE
    c5_0_376 = TRUE
    c6_0_377 = TRUE
    c2_17_377 = TRUE
    c3_10_752 = TRUE
    c2_17_376 = FALSE
    c6_0_376 = FALSE
    c5_0_377 = TRUE
  -- Loop starts here
  -> State: 1.2 <-
    c3_10_752 = FALSE
    c2_17_376 = TRUE
    c6_0_376 = TRUE
  -> State: 1.3 <-
"""

if __name__ == "__main__":

    monitored = {'c2_17_376': 'c2',
                 'c2_17_377': 'c2',
                 'c6_0_376': 'c6',
                 'c6_0_377': 'c6',
                 'c5_0_376': 'c5',
                 'c5_0_377': 'c5'}

    print parse_counterexample(STR, monitored)

