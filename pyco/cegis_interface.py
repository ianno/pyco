'''
This module includes the interface classes and functions for the Z3 SMT solver

Author: Antonio Iannopollo
'''

# import logging
import itertools
from time import time

import multiprocessing
from pyco.contract import CompositionMapping
from pyco import LOG
from pyco.synthesis_manager import ModelVerificationManager, MAX_THREADS
# from pyco.smt_factory import SMTModelFactory
# from pyco.z3_library_conversion import Z3Library
from pyco.cegis_single_port_solver import SinglePortSolver, NotSynthesizableError, OptimizationError
from pyco.spec_decomposition import decompose_spec
from pyco.graphviz_converter import GraphCreator, GraphizConverter

# LOG = logging.getLogger()
LOG.debug('in cegis_interface')


class CegisInterface(object):
    '''
    Extends the class SMTModelFactory
    '''

    def __init__(self, library):
        '''
        init
        '''

        #set_param(proof=False)
        self.library = library
        # selfeset = library.typeset
        self.type_compatibility_set = library.type_compatibility_set
        self.type_incompatibility_set = library.type_incompatibility_set

        # constraints by components
        self.distinct_ports_by_component = {}

        # hints from designer
        self.same_block_constraints = None
        self.distinct_mapping_constraints = None

        self.fixed_components = None
        self.fixed_connections = None
        self.fixed_connections_spec = None

        self.solver = None
        self.specification_list = []
        self.spec = None


        # self.lib_model = Z3Library(self.library)



    # def initiliaze_solver(self, spec):
    #     '''
    #     Create environment and models from library
    #     '''

    #     self.lib_model.preprocess_spec(spec)
    #     self.lib_model.instantiate_models()


    # def init_models(self):
    #     '''
    #     basic constraints
    #     :return:
    #     '''


    #     constraints = []
    #     constraints += [Or(comp == 0, comp == 1) for comp in self.lib_model.use_flags.values()]
    #     #constraints += [lev >= 0 for lev in self.lib_model.level_index.values()]

    #     return And(constraints)

    # def use_max_n_components(self, n):
    #     '''
    #     Force the solver to use up to n components for a candidate solution
    #     '''

    #     constraints = []

    #     # limit the values
    #     constraints += [Sum(self.lib_model.use_flags.values()) <= n]

    #     # LOG.debug(constraints)
    #     # self.solver.add(constraints)
    #     return And(constraints)

    # # def type_connection_rules(self):
    # #     '''
    # #     Force the solver to include related components if a component is chosen
    # #     '''
    # #
    # #     constraints = []
    # #
    # #     # limit the values
    # #     for contract in self.library.all_contracts:
    # #         options = []
    # #         for opt in self.library.connection_map[contract]:
    # #             single_conf = [self.lib_model.use_flags[c]==1 for c in opt]
    # #             options.append(And(single_conf))
    # #
    # #         constraints.append(Implies(self.lib_model.use_flags[contract]==1,
    # #                                    Or(options)))
    # #
    # #     LOG.debug(constraints)
    # #     # self.solver.add(constraints)
    # #     return And(constraints)

    # def type_connection_rules_and_no_loops(self):
    #     '''
    #     Force the solver to include related components if a component is chosen
    #     '''

    #     constraints = []
    #     #LOG.debug(self.library.connection_map)
    #     # limit the values
    #     for contract in self.library.all_contracts - self.library.incompatible_components:
    #         options = []
    #         for opt in self.library.connection_map[contract]:
    #             single_conf = [And(self.lib_model.use_flags[c] == 1,
    #                                self.lib_model.level_index[c] < self.lib_model.level_index[contract])
    #                            for c in opt - self.library.incompatible_components]
    #             if len(single_conf) > 0:
    #                 options.append(And(single_conf))
    #             else:
    #                 options.append(True)

    #         constraints.append(Implies(self.lib_model.use_flags[contract] == 1,
    #                                    Or(options)))

    #     # LOG.debug(constraints)
    #     # self.solver.add(constraints)
    #     return And(constraints)

    # def type_connection_rules(self):
    #     '''
    #     Force the solver to include related components if a component is chosen
    #     '''

    #     constraints = []
    #     #LOG.debug(self.library.connection_map)
    #     # limit the values
    #     for contract in self.library.all_contracts - self.library.incompatible_components:
    #         options = []
    #         for opt in self.library.connection_map[contract]:
    #             single_conf = [self.lib_model.use_flags[c] == 1
    #                            for c in opt - self.library.incompatible_components]
    #             if len(single_conf) > 0:
    #                 options.append(And(single_conf))
    #             else:
    #                 options.append(True)

    #         constraints.append(Implies(self.lib_model.use_flags[contract] == 1,
    #                                    Or(options)))

    #         # #now force all contracts not in right config to be 0:
    #         # clist = []
    #         # for conf in self.library.depending_on[contract]:
    #         #     f = And([self.lib_model.use_flags[c] == 1 for c in conf])
    #         #     clist.append(f)
    #         #
    #         # if len(clist) > 0:
    #         #     f = Not(Or(clist))
    #         # else:
    #         #     f = True
    #         # constraints.append(Implies(f, self.lib_model.use_flags[contract] == 0))

    #     # LOG.debug(constraints)
    #     # self.solver.add(constraints)
    #     return And(constraints)

    # def process_fixed_components(self):
    #     '''
    #     Force the solver to include related components if a component is chosen
    #     '''

    #     #constraints = []
    #     #LOG.debug(self.library.connection_map)
    #     # limit the values
    #     constraints = [self.lib_model.use_flags[c] == 1 for c in self.retrieve_fixed_components()]

    #     # LOG.debug(constraints)
    #     # self.solver.add(constraints)
    #     return And(constraints)

    def retrieve_fixed_components(self):
        '''
        returns a set of fixed components
        :return:
        '''
        seen = set()
        for c, l in self.fixed_components:
            comp = self.library.contract_map[c.base_name]
            el = self.library.components[comp][l]
            seen.add(el)

        return seen

    # def max_depth(self, n):
    #     '''
    #     Set max depth of solution
    #     '''
    #     # constraints = []

    #     # limit the values
    #     constraints = [lev <= n for lev in self.lib_model.level_index.values()]

    #     # LOG.debug(constraints)
    #     # self.solver.add(constraints)
    #     return And(constraints)

    # def solve_for_outputs(self, outputs, context):
    #     '''
    #     Solve the synthesis problem only for the 'outputs' set spec ports
    #     :param outputs:
    #     :return:
    #     '''

    #     constraints = []

    #     # limit the values
    #     for port in outputs:
    #         options = [self.lib_model.use_flags[c] == 1
    #                         for c in self.library.spec_out_map[port]]

    #         constraints.append(And(options, context))

    #     #LOG.debug(constraints)
    #     # self.solver.add(constraints)
    #     return And(constraints, context)

    def synthesize(self, specs,
                   distinct_spec_port_set=None,
                   limit=None,
                   max_depth=None,
                   minimize_components=False,
                   minimize_cost=False,
                   fixed_components=None,
                   fixed_connections=None,
                   fixed_connections_spec=None,
                   balance_types=None,
                   decompose=True):
        '''
        perform synthesis process
        '''
        if sum([minimize_components, minimize_cost]) > 1:
            raise OptimizationError('Only one objective can be minimized')
        if minimize_cost:
            raise NotImplementedError('Custom cost not yet implemented')

        #self.time = {}
        #self.time['start'] = time()

        self.distinct_spec_port_set = {}
        if distinct_spec_port_set is not None:
            self.distinct_spec_port_set = distinct_spec_port_set

        self.fixed_components = fixed_components
        self.fixed_connections = fixed_connections
        self.fixed_connections_spec = fixed_connections_spec

        self.specification_list = specs

        optimize = minimize_components | minimize_cost

        # let's pick a root
        # we assume all the specs have same interface
        self.spec = self.specification_list[0]
        spec_outs = len(self.spec.output_ports_dict)

        if limit is None:
            self.max_components = spec_outs
        else:
            self.max_components = limit

        # if depth is None:
        #     depth = min(int(3* limit/spec_outs), limit)
        self.max_depth = max_depth


        self.balance_max_types = set()
        if balance_types is not None:
            self.balance_max_types = balance_types

        # constraints = [True]

        # self.initiliaze_solver(self.spec)
        self.library.preprocess_with_spec(self.spec)


        # print lib structure
        for contract in self.library.all_contracts:
            LOG.debug('++++')
            LOG.debug('%s' % (contract.base_name))


        # constraints.append(self.init_models())
        #constraints.append(self.use_max_n_components(self.max_components))
        #constraints.append(self.max_depth(depth))
        # constraints.append(self.type_connection_rules())
        # constraints.append(self.type_connection_rules_and_no_loops())

        # constraints.append(self.process_fixed_components())

        # goal = Goal()
        # goal.add(constraints)
        # goal = goal.simplify()

        # #split here
        # if optimize:
        #     solv = Optimize()
        # else:
        #     solv = Solver()

        # solv.add(goal.as_expr())

        # self.base_solver = solv

        if decompose:
            print('Decomposing Specification...')
            clusters = decompose_spec(self.specification_list, self.library)
        else:
            clusters = [self.spec.output_ports_dict.keys()]

        print(clusters)

        if len(clusters) == 0:
            clusters.append([])

        print('Instantiate Solvers...')
        #create parallel solvers
        solvers = []

        result_queue = multiprocessing.Queue()

        semaphore = multiprocessing.Semaphore(MAX_THREADS)

        results = []

        for cluster in clusters:
        # for cluster in [['o1', 'o2', 'o3']]:
        # for cluster in [['c2','c3','c5','c6']]:

            #solve for port
            # self.base_solver.push()

            # self.base_solver.add(self.solve_for_outputs(cluster))

            # context = Context()
            # assertions = self.base_solver.assertions()
            # new_assertions = assertions.translate(context)

            #restore solver state
            # self.base_solver.pop()

            solver_p = SinglePortSolver(self,
                                        cluster, semaphore,
                                        self.spec,
                                        minimize_components=minimize_components,
                                        distinct_spec_port_set=None,
                                        fixed_components=self.fixed_components,
                                        fixed_connections=self.fixed_connections,
                                        fixed_connections_spec=self.fixed_connections_spec,
                                        result_queue=result_queue,
                                        )

            solvers.append(solver_p)

            solver_p.start()
            # solver_p.join()


        while len(results) < len(clusters):
            results.append(result_queue.get())
            if results[-1] is None:
                break

        if any([x is None for x in results]):
            raise NotSynthesizableError


        #print
        LOG.debug("merging solutions...")


        new_graph = GraphCreator.merge_graphs(results, '_'.join(self.spec.output_ports_dict.keys()))
        gv = GraphizConverter.generate_graphviz_from_generic_graph(new_graph)
        gv.view()
        # gv.save()

        #wait for clean exit
        for solv in solvers:
           solv.join()


# SMTModelFactory.register(SynthesisInterface)
