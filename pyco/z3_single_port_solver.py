'''
This module includes classess and methods to synthesize a solution for a single port of the specification.
Each solver has its own process

Author: Antonio Iannopollo
'''

import pyco
from pyco import LOG
import itertools
from time import time

import types
from z3 import *
import multiprocessing

from pycolite.contract import CompositionMapping
from pyco.z3_thread_manager import MAX_THREADS, ModelVerificationManager
from pyco.z3_library_conversion import Z3Library
# from threading import Thread
from multiprocessing import Pool, Process, Queue
# from Queue import Queue

import time

# MAX_SOLVERS = 10

class SinglePortSolver(multiprocessing.Process):
    '''
    this process synthesizes a solution for a single output port
    '''

    def __init__(self, z3_interface, assertions,
                 context,
                 spec_port_names, semaphore, spec,
                 minimize_components=False,
                 distinct_spec_port_set=None,
                 fixed_components=None,
                 fixed_connections=None,
                 fixed_connections_spec=None,
                 result_queue=None,
                 ):

        # set_option(verbose=15)
        # set_option(proof=False)

        self.z3_interface = z3_interface
        self.max_depth = z3_interface.max_depth

        self.type_compatibility_set = z3_interface.type_compatibility_set
        self.type_incompatibility_set = z3_interface.type_incompatibility_set

        self.semaphore = semaphore

        self.spec = spec
        self.context = context
        self.assertions = assertions
        self.spec_port_names = spec_port_names
        self.spec_out_dict = self.spec.output_ports_dict

        self.num_out = len(self.spec_out_dict)

        self.lib_model = self.z3_interface.lib_model
        self.library = self.z3_interface.library

        self.lib_model.instantiate_models(context=self.context)


        self.specification_list = self.z3_interface.specification_list

        optimize = minimize_components

        self.distinct_spec_port_set = {}
        if distinct_spec_port_set is not None:
            self.distinct_spec_port_set = distinct_spec_port_set

        self.fixed_components = {}
        if fixed_components is not None:
            self.fixed_components = fixed_components

        self.fixed_connections = {}
        if fixed_connections is not None:
            self.fixed_connections = fixed_connections
        self.fixed_connections_spec = {}
        if fixed_connections_spec is not None:
            self.fixed_connections_spec = fixed_connections_spec


        self.solver = Solver(ctx=self.context)
        # self.solver = Then('simplify', 'bit-blast', 'split-clause',
        #                    'qfbv', 'sat', ctx=self.context).solver()

        # self.solver = Then('simplify', 'smt', ctx=self.context).solver()
        # self.solver = Tactic('qflia', ctx=self.context).solver()#Solver(ctx=self.context)

        if optimize:
            self.solver = Optimize(ctx=self.context)


        #LOG.debug(self.assertions)
        self.solver.add(self.assertions)
        self.solver.add(self.z3_interface.solve_for_outputs(spec_port_names, context))


        if minimize_components:
            LOG.debug('minimize components')
            self.obj_c = self.solver.minimize(Sum(self.lib_model.use_flags.values()))


        self.result_queue = result_queue
        # set seed
        # self.solver.set('seed', 12345)


        super(SinglePortSolver, self).__init__()


    def add_assertions(self, assertions):
        '''
        add constraints to solver
        :param assertions:
        :return:
        '''

        self.solver.add(assertions)
        return

        # #to avoid incremental solving, we recreate a new solver each time
        # old_assrt = self.solver.assertions()
        #
        # self.solver = Tactic('qflia', ctx=self.context).solver()
        #
        # self.solver.add(old_assrt)
        # self.solver.add(assertions)
        # return

    def run(self):


        initial_size = self.z3_interface.max_components

        size = initial_size
        if MAX_THREADS >= 1:
            thread_manager = ModelVerificationManager(self, self.spec_port_names, self.semaphore)

            try:
                (model, composition,
                 spec, contract_list, params_assign) = thread_manager.synthesize()
            except NotSynthesizableError:
                self.result_queue.put(None)
                raise
            else:
                # LOG.info(model)
                # for c in contract_list:
                #     LOG.debug(c)
                # LOG.info(spec)
                # LOG.info(composition)

                # from graphviz_converter import GraphizConverter
                # graphviz_conv = GraphizConverter(spec, composition, contract_list, parameters_values=params_assign, filename='_'.join(self.spec_port_names))
                # graphviz_conv.generate_graphviz()
                # graphviz_conv.view()

                from graphviz_converter import GraphCreator, GraphizConverter
                graph = GraphCreator(spec, composition, contract_list, parameters_values=params_assign, filename='_'.join(self.spec_port_names))
                graph = graph.generate_graph()

                self.result_queue.put(graph)
                gv = GraphizConverter.generate_graphviz_from_generic_graph(graph)
                gv.view()

                return model, composition, spec, contract_list, params_assign

                # return model, composition, spec, contract_list
        else:
            while True:
                try:
                    model = self.propose_candidate()
                except NotSynthesizableError as err:
                    raise err
                else:
                    try:
                        composition, spec, contract_list = self.verify_candidate(model, self.spec_port_names)
                    except NotSynthesizableError as err:
                        LOG.debug("candidate not valid")
                    else:
                        LOG.info(model)
                        for c in contract_list:
                            LOG.debug(c)
                        LOG.info(self.spec)
                        LOG.info(composition)
                        return model, composition, spec, contract_list


    def verify_candidate(self, model, output_port_name):
        '''
        check if a candidate is valid or not.
        Here we need to:
        1) transform the model to a contract composition
        2) LEARN
            2a)
        '''

        # self.reject_candidate(model, candidates)
        state, composition, connected_spec, contract_inst, failed_spec = \
            self.check_all_specs(model, output_port_name)
        if not state:
            # learn
            # as first step, we reject the actual solution
            # self.solver.add(self.exclude_candidate_type())
            # LOG.debug('exclude')
            # LOG.debug(z3.Not(self.connected_ports==model[self.connected_ports]))
            # self.solver.add(z3.Not(self.connected_ports==model[self.connected_ports]))
            # self.reject_candidate(model, failed_spec)
            self.reject_candidate(model)

            # then check for consistency
            # self.solver.add(self.check_for_consistency(model, contract_inst, connected_spec))

            raise NotSynthesizableError

        return composition, connected_spec, contract_inst

    def propose_candidate(self):
        '''
        generate a model
        '''

        res = self.solver.check()
        # LOG.debug(self.solver.upper(self.obj))
        # LOG.debug(self.solver.lower(self.obj))
        # LOG.debug(res)
        if res == sat:
            # LOG.debug(self.solver.model())
            # LOG.debug(self.solver.model()[self.fully_connected])
            pass
        else:
            raise NotSynthesizableError()

        try:
            model = self.solver.model()
        except Z3Exception:

            raise NotSynthesizableError()
        else:
            pass
            ##for spec in self.spec_ins:
            ##    LOG.debug('%s -> %s'
            ##        % (spec, self.lib_model.model_by_index(simplify(model[spec]).as_long())))
            # for spec in self.spec_outs:
            #    LOG.debug('%s -> %s'
            #        % (spec, self.lib_model.model_by_index(simplify(model[spec]).as_long())))

            # LOG.debug(model)

        return model

    # def check_all_specs(self, model, output_port_name):
    #     '''
    #     check if the model satisfies a number of specs, if provided
    #     :param output_port_name:
    #     '''
    #     composition = None
    #     connected_spec = None
    #     contract_inst = None
    #     failed_spec = None
    #     for spec in self.specification_list:
    #         composition, connected_spec, contract_inst = \
    #             self.build_composition_from_model(model, spec, output_port_name)
    #
    #         if not composition.is_refinement(connected_spec):
    #             LOG.debug('ref check done 1')
    #             failed_spec = spec
    #             return False, composition, connected_spec, contract_inst, failed_spec
    #
    #         LOG.debug('ref check done 2')
    #
    #     return True, composition, connected_spec, contract_inst, None

    def _infer_relevant_contracts(self, model, output_port_names):
        '''
        Infer the valid configurations represented by the current model
        NOTE: we need this function to "crawl" from the outputs to the actual
        possible components to avoid the solver providing the same solution with only
        some irrelevant components which are different.

        TODO:
        clean this

        :param model:
        :param output_port_names:
        :return:
        '''

        connection_map = self.lib_model.library.connection_map
        spec_map = self.lib_model.library.spec_out_map


        #configurations = {}
        processing = []

        all_contracts_in_model = {x
                                  for x, m in self.lib_model.use_flags.items()
                                  if model[m].as_long() == 1}


        #start from the outputs, and go backward to map all the possible configs

        # for spec_out in output_port_names:
        #     configurations[spec_out] = {x: [] for x in spec_map[spec_out] if x in all_contracts_in_model}


        seen = set()
        seen |= self.retrieve_fixed_components()

        configurations = {x: [] for spec_out in output_port_names for x in spec_map[spec_out] if x in all_contracts_in_model}

        fixed_conf = {c: [] for c in seen }

        configurations.update(fixed_conf)

        for x in configurations:
        #x is a contract

            seen.add(x)
            used = {x}
                    #from each port we create levels navigating backwards
            self.__find_configurations_for_contract(seen, used, x, all_contracts_in_model,
                                                            connection_map,
                                                            configurations[x])



        # LOG.debug(all_contracts_in_model - seen)
        return seen, configurations


    def retrieve_fixed_components(self):
        '''
        return fixed components
        :return:
        '''
        return self.z3_interface.retrieve_fixed_components()

    def __find_configurations_for_contract(self, seen, used, contract,
                                           all_contracts, connection_map, upper_list):
        '''
        fill possible configurations dict up to a certain depth
        :param depth:
        :param contract:
        :param all_contracts:
        :param connection_map:
        :return:
        '''


        for conf in connection_map[contract]:
            if conf <= (all_contracts - used):

                conf_dict = {}

                for c in conf - seen:
                    seen.add(c)
                    c_list = []
                    self.__find_configurations_for_contract(seen, used | {c}, c,
                                                            all_contracts,
                                                            connection_map,
                                                            c_list)

                    conf_dict[c] = c_list


                if len(conf_dict) > 0:
                    upper_list.append(conf_dict)

        return

    def generate_reject_formula(self, used_contracts):

        '''
        generate compact reject formula

        :param seen_contracts:
        :return:
        '''


        seen = set()
        constraints = []

        #process ports


        for x in used_contracts:

            if x not in seen:

                x_inst = {c for c in used_contracts
                          if c.base_name == x.base_name}

                # append current contract and its siblings
                all_cs = self.library.contracts_by_name(x.base_name)
                use_f = Or([self.lib_model.use_flags[q] == 1
                            for q in all_cs], self.context)

                # rej_single_p.append(Or([self.lib_model.use_flags[q] == 1
                #                     for q in all_cs], self.context))

                if len(x_inst) > 0:
                    m_inst = [self.lib_model.use_flags[c] for c in all_cs]
                    use_f = And(use_f, Sum(m_inst) <= len(x_inst), self.context)

                constraints.append(use_f)

                for c in x_inst:
                    seen.add(c)


                #process missing configs


                for c in x_inst:
                    #c_inner = []
                    all_configs = self.library.depending_on[c]
                    for conf in all_configs:
                        inner = []
                        diff = conf - used_contracts
                        if len(diff) > 0:

                            for s in diff:
                                inner.append(self.lib_model.use_flags[s] == 0)

                        if len(inner) > 0:
                            constraints.append(Or(inner, self.context))

                    #The following is useful
                    all_spec_configs = self.library.spec_depending_on[c]
                    for conf in all_spec_configs:
                        inner = []
                        diff = conf - used_contracts
                        if len(diff) > 0:

                            for s in diff:
                                # s_inst = {c for c in used_contracts
                                #          if c.base_name == s.base_name}
                                # all_s = self.library.contracts_by_name(s.base_name)
                                # use_s = Or([self.lib_model.use_flags[q] == 0
                                #           for q in all_s], self.context)

                                # if len(s_inst) > 0:
                                #    m_inst = [self.lib_model.use_flags[c] for c in all_s]
                                #    use_s = And(use_s, Sum(m_inst) != len(s_inst), self.context)

                                # LOG.debug(conf)
                                inner.append(self.lib_model.use_flags[s] == 0)

                        if len(inner) > 0:
                            constraints.append(And(inner, self.context))


        rej_ = Not(And(constraints, self.context), self.context)
        rej = simplify(rej_)

        return rej



    def _infer_relevant_ports_from_model(self, model, output_port_names):
        '''
        Create a list of contracts connected to the spec, eliminating spurious results

        :param model:
        :param spec:
        :param output_port_name:
        :return:
        '''

        # now we need to collect all the components connected in chain to the spec output we are considering
        # we start with the model connected to the out
        spec_port_models = [self.spec_out_dict[name] for name in output_port_names]
        models = []

        to_process = [self.lib_model.model_by_index(model[mod].as_long()) for mod in spec_port_models]
        done = []
        spec_models = []

        while len(to_process) > 0:
            m = to_process.pop()
            done.append(m)

            # find related input models
            comp_models = [mod for mod in self.lib_model.related_models(m) if model[mod] is not None and model[mod].as_long() > -1]

            # find models these are connected to
            connected_models = [self.lib_model.model_by_index(model[port].as_long()) for port in comp_models
                                if (-1 < model[port].as_long() < self.lib_model.specs_at)]

            spec_models += [port for port in comp_models
                            if port not in connected_models and model[port].as_long() >= self.lib_model.specs_at]

            # add to the main list
            models += comp_models
            models += connected_models

            # add for further processing
            for mod in connected_models:
                if mod not in done:
                    to_process.append(mod)

        return set(models), set(spec_models)

    def __infer_contract_dependency(self, model, output_port_names):
        '''
        Create a list of contracts connected to the spec, eliminating spurious results

        :param model:
        :param spec:
        :param output_port_name:
        :return:
        '''

        # now we need to collect all the components connected in chain to the spec output we are considering
        # we start with the model connected to the out
        spec_port_models = [self.spec_out_dict[name] for name in output_port_names]
        models = []

        to_process = [self.lib_model.model_by_index(model[mod].as_long()) for mod in spec_port_models]
        done = []

        dep = {}

        spec_models = []

        while len(to_process) > 0:
            m = to_process.pop()
            done.append(m)

            lev = -1

            if self.lib_model.index_by_model(m) < self.lib_model.specs_at:
                lev, contract = self.lib_model.contract_by_model(m)

            # find related input models
            comp_models = [mod for mod in self.lib_model.related_models(m) if model[mod] is not None and model[mod].as_long() > -1]

            # find models these are connected to
            connected_models = [self.lib_model.model_by_index(model[port].as_long()) for port in comp_models
                                if (-1 < model[port].as_long() < self.lib_model.specs_at)]

            spec_models = [port for port in comp_models
                            if port not in connected_models and model[port].as_long() >= self.lib_model.specs_at]

            if lev > -1:
                if (lev, contract) not in dep:
                    dep[(lev, contract)] = set()

                for mod in connected_models + spec_models:
                    m_lev, m_contract = self.lib_model.contract_by_model(mod)

                    if ((lev, contract)) != ((m_lev, m_contract)):
                        dep[(lev, contract)].add((m_lev, m_contract))


            # add for further processing
            for mod in connected_models:
                if mod not in done:
                    to_process.append(mod)

        return dep


    def build_composition_from_model(self, model, output_port_names, relevant_contracts, var_assign, params=None, build_copy=False):
        '''
        builds a contract composition out of a model
        :param output_port_name:
        '''


        spec = self.spec.copy()
        working_spec = spec.copy()

        processed_ports = set()
        used_contracts = set()

        #used for copies, maps to itself if not a copy
        relevant_map = {c: c for c in relevant_contracts}

        if build_copy:
            relevant_copies = {x:x.copy() for x in relevant_contracts}
            relevant_map = {p:c for c,p in relevant_copies.items()}

            relevant_contracts = { c for c in relevant_copies.values()}

            uname_map = {p.unique_name: relevant_copies[c].ports_dict[p.base_name].unique_name
                         for c in relevant_copies for p in c.ports_dict.values()}

            var_c = var_assign
            var_assign = copy.deepcopy(var_c)

            for un in var_c:
                name = un
                if un in uname_map:
                    name = uname_map[un]
                    var_assign[name] = var_c[un]
                    del var_assign[un]


                uun = var_c[un]
                if uun in uname_map:
                    var_assign[name] = uname_map[uun]

            if params is not None:
                params = {uname_map[uname]: params[uname] for uname in params}




        mapping = CompositionMapping(relevant_contracts| {working_spec})

        temp_spec_used = False

        #TODO move it at the end
        #process working spec
        # for port in working_spec.ports_dict.values():
        #     name = port.base_name
        #
        #     if name not in output_port_names:
        #         if port.is_output:
        #             temp_spec_used = True
        #         spec.connect_to_port(spec.ports_dict[name], port)

        # start with spec
        for bname in output_port_names:
            port = spec.ports_dict[bname]
            for c in relevant_contracts:
                done = False

                for obname, oport in c.output_ports_dict.items():
                    ouname = oport.unique_name

                    if bname in var_assign:
                        if ouname == var_assign[bname]:
                            spec.connect_to_port(port, oport)
                            done = True
                            used_contracts.add(c)
                            break
                    else:
                        #pick any other port
                        if c in self.library.spec_out_map[bname]:
                            if self.library.check_connectivity(port, oport):
                                spec.connect_to_port(port, oport)
                                done = True
                                used_contracts.add(c)
                                break

                if done:
                    break

        stack = {x for x in used_contracts}

        # connections among candidates
        while len(stack) > 0:
            c1 = stack.pop()
            used_contracts.add(c1)

            for n1, p1 in c1.input_ports_dict.items():
                u1 = p1.unique_name
                done = False
                for c2 in relevant_contracts:

                    done = False
                    if u1 in var_assign:
                        for n2, p2 in c2.output_ports_dict.items():
                            u2 = p2.unique_name

                            if u2 == var_assign[u1]:
                                mapping.connect(p1, p2,
                                                '%s_%s' % (c1.unique_name,
                                                           p1.base_name))
                                done = True
                                processed_ports.add(p1)
                                processed_ports.add(p2)
                                if c2 not in used_contracts:
                                    stack.add(c2)
                                break

                    else:
                        for conf in self.library.connection_map[relevant_map[c1]]:
                            if relevant_map[c2] in conf:
                                for n2, p2 in c2.output_ports_dict.items():
                                    u2 = p2.unique_name
                                    if self.library.check_connectivity(p1, p2):
                                        mapping.connect(p1, p2,
                                                        '%s_%s' % (c1.unique_name,
                                                                   n1))
                                        done = True
                                        processed_ports.add(p1)
                                        processed_ports.add(p2)
                                        if c2 not in used_contracts:
                                            stack.add(c2)
                                        break
                                if done:
                                    break
                    if done:
                        break

                #spec
                if not done:
                    for n2, p2 in spec.input_ports_dict.items():

                        if u1 in var_assign and n2 == var_assign[u1]:
                            spec.connect_to_port(p2, p1)
                            processed_ports.add(p1)
                            processed_ports.add(p2)
                            break

        if build_copy:
            relevant_contracts = used_contracts | {relevant_copies[x] for x in self.retrieve_fixed_components()}
        else:
            relevant_contracts = used_contracts | self.retrieve_fixed_components()

        for c in relevant_contracts:
            for p in c.ports_dict.values():
                if p not in processed_ports:
                    mapping.add(p, '%s_%s' % (c.unique_name,
                                                         p.base_name))
                    processed_ports.add(p)

        #     if model[p_model] is not None:
        #         level, old_contract = self.lib_model.contract_by_model(p_model)
        #         current_contract = contract_map[(level, old_contract)]
        #         old_port = self.lib_model.port_by_model(p_model)
        #         current_port = current_contract.ports_dict[old_port.base_name]
        #
        #         if p_model.get_id() in model_index_map:
        #             other_index = model_index_map[p_model.get_id()]
        #         else:
        #             other_index = model[p_model].as_long()
        #
        #         if other_index < self.lib_model.specs_at:
        #
        #             other_mod = self.lib_model.models[other_index]
        #             other_level = self.lib_model.model_levels[other_mod.get_id()]
        #
        #             other_port_orig = self.lib_model.port_by_index(other_index)
        #
        #             oi = model[p_model].as_long()
        #             om = self.lib_model.models[oi]
        #             ol = self.lib_model.model_levels[om.get_id()]
        #
        #             # LOG.debug(other_level)
        #             # LOG.debug(other_port_orig.base_name)
        #             # LOG.debug(ol)
        #             # LOG.debug(self.lib_model.port_by_index(oi).base_name)
        #
        #
        #             # LOG.debug(other_index)
        #             # LOG.debug(other_port_orig.base_name)
        #
        #             other_contract = contract_map[(other_level, other_port_orig.contract)]
        #
        #             other_port = other_contract.ports_dict[other_port_orig.base_name]
        #
        #             # LOG.debug(other_port.base_name)
        #             mapping.connect(current_port, other_port,
        #                             '%s_%d_%s' % (current_contract.unique_name, level,
        #                                        current_port.base_name))
        #
        #             processed_ports.add(current_port)
        #             processed_ports.add(other_port)
        #
        #
        # # add all the remaining names to new composition
        # for (level, old_contract) in contract_map.keys():
        #     for old_port in old_contract.ports_dict.values():
        #         current_contract = contract_map[(level, old_contract)]
        #         current_port = current_contract.ports_dict[old_port.base_name]
        #         if current_port not in processed_ports:
        #             mapping.add(current_port, '%s_%d_%s' % (current_contract.unique_name, level,
        #                                                  current_port.base_name))
        #             processed_ports.add(current_port)
        #
        # # for contract in contracts:
        # #    LOG.debug(contract)
        # # LOG.debug(working_spec)
        # # LOG.debug(spec_contract)
        #
        # # if not complete_model:
        # #    c_set = self.filter_candidate_contracts_for_composition(contracts, spec_contract)
        #
        # # compose
        # #root = contracts.pop()
        #
        # # c_set.add(root.copy())
        #
        if temp_spec_used:
            composition = working_spec.compose(relevant_contracts, composition_mapping=mapping)
        else:
            root = relevant_contracts.pop()
            composition = root.compose(relevant_contracts, composition_mapping=mapping)
            relevant_contracts.add(root)

        LOG.debug(composition)
        for c in relevant_contracts:
            LOG.debug(c)

        if params is None:
            return composition, spec, relevant_contracts
        else:
            return composition, spec, relevant_contracts, params



    # def recursive_reject_formula_no_ca(self, current_contract, current_level, shift,
    #                              contract_model_map, model,
    #                              pending_equalities,
    #                              previous_contracts, next_contracts,
    #                              shift_map, output_port_names):
    #     '''
    #     build compact reject formula using recursion.
    #     The current contract needs to fix all the equalities with ports
    #     of contracts which came before it, and leave the evaluation of
    #     model equalities with contracts with order less than this.
    #     :return:
    #     '''
    #
    #     # check if this formula has already been computed
    #     # if reject_map[current_contract][] # TODO
    #
    #
    #     # equalities = {lev: set() for lev in range(self.lib_model.max_components)}
    #
    #
    #     equalities = set()
    #
    #     # if current_contract == self.spec_contract:
    #     #
    #     #     #spec is always the last one, all its connections are in previous contracts
    #     #     assert False#len(next_contracts) == 0
    #     #
    #     #
    #     #     for name in output_port_names:
    #     #         mod = self.spec_out_dict[name]
    #     #
    #     #         m_index = model[mod].as_long()
    #     #         m_mod = self.lib_model.model_by_index(m_index)
    #     #
    #     #         m_lev, m_contract = self.lib_model.contract_by_model(m_mod)
    #     #
    #     #         # contract shift
    #     #         # LOG.debug(m_index)
    #     #         # LOG.debug(shift_map)
    #     #         m_shift = shift_map[(m_lev, m_contract)]
    #     #         shifted_ind = self.lib_model.index_shift(m_index, m_shift)
    #     #
    #     #         equalities.add(mod == shifted_ind)
    #     #
    #     #
    #     # else:
    #
    #     current_out_indices = set(self.lib_model.contract_out_indices(current_contract)[current_level])
    #
    #     # relevant_in_mod = self.lib_model.relevant_input_models(current_level, current_contract)
    #
    #     # LOG.debug(relevant_in_mod)
    #     # relevant_in_idx = self.lib_model.relevant_input_indices(current_level, current_contract)
    #     #
    #     # relevant_out_mod = self.lib_model.relevant_output_models(current_level, current_contract)
    #     # relevant_out_idx = self.lib_model.relevant_output_indices(current_level, current_contract)
    #
    #     for mod in contract_model_map[(current_level, current_contract)]:
    #     # for mod in relevant_in_mod:
    #
    #         # LOG.debug(mod)
    #         # LOG.debug(current_level)
    #         # LOG.debug(current_contract.base_name)
    #         m_index = model[mod].as_long()
    #
    #         if m_index >= self.lib_model.specs_at:
    #             #this is connected to spec
    #             equalities.add(mod == m_index)
    #         else:
    #             m_mod = self.lib_model.model_by_index(m_index)
    #             m_lev, m_contract = self.lib_model.contract_by_model(m_mod)
    #
    #             if (m_lev, m_contract) in previous_contracts:
    #                 # contract shift
    #                 # LOG.debug(m_index)
    #                 # LOG.debug(shift_map)
    #                 m_shift = shift_map[(m_lev, m_contract)]
    #                 shifted_ind = self.lib_model.index_shift(m_index, m_shift)
    #
    #                 equalities.add(mod == shifted_ind)
    #
    #             else:
    #                 #else add to pending
    #                 if m_index not in pending_equalities:
    #                     pending_equalities[m_index] = set()
    #                 pending_equalities[m_index].add(mod)
    #
    #
    #     #now all the above models which have indices which are of this contract
    #     for idx in pending_equalities.keys():
    #         if idx in current_out_indices:
    #             mods = pending_equalities[idx]
    #
    #             shifted_ind = self.lib_model.index_shift(idx, shift)
    #
    #             for mod in mods:
    #                 equalities.add(mod == shifted_ind)
    #
    #             # reset pending
    #             pending_equalities.pop(idx)
    #
    #
    #     #assemble results
    #     if len(next_contracts) > 0:
    #         #pick next contract
    #         (next_lev, next_c) = next_contracts.pop(0)
    #
    #         inner_shifts = []
    #         # independent = False
    #         #
    #         # if (current_level, current_contract) not in dep_lookup[(next_lev, next_c)]:
    #         #     independent = True
    #
    #         for shift in range(self.lib_model.max_components):
    #
    #             check_dep = [((current_level, current_contract))]+[(l,c) for (l,c) in previous_contracts]
    #             new_shifts = {(current_level, current_contract): shift}
    #             new_shifts.update(shift_map)
    #             pending_eq = {idx: set([x for x in eq_set]) for (idx, eq_set) in pending_equalities.items()}
    #             next_ctr = [(lev, ctr) for (lev, ctr) in next_contracts]
    #             prev_ctr = [(lev, ctr) for (lev, ctr) in previous_contracts]
    #
    #             inner_shifts.append(self.recursive_reject_formula_no_ca(next_c, next_lev, shift, contract_model_map,
    #                                                                 model, pending_eq,
    #                                                                 prev_ctr + [(current_level, current_contract)],
    #                                                                 next_ctr,
    #                                                                 new_shifts,
    #                                                               output_port_names))
    #         inner_formula = Or(inner_shifts, self.context)
    #         # if len(equalities | set([inner_formula])) == 0:
    #         #     rej_formula = True
    #         # else:
    #
    #         rej_formula = And(equalities | set([inner_formula]), self.context)
    #     else:
    #         if len(equalities) == 0:
    #             rej_formula = True
    #         else:
    #             rej_formula = And(equalities, self.context)
    #
    #
    #     return rej_formula

    def recursive_reject_formula(self, current_contract, current_level, shift,
                                 contract_model_map, model,
                                 pending_equalities,
                                 previous_contracts, next_contracts,
                                 shift_map, output_port_names):
        '''
        build compact reject formula using recursion.
        The current contract needs to fix all the equalities with ports
        of contracts which came before it, and leave the evaluation of
        model equalities with contracts with order less than this.
        :return:
        '''

        # check if this formula has already been computed
        # if reject_map[current_contract][] # TODO


        # equalities = {lev: set() for lev in range(self.lib_model.max_components)}


        equalities = set()

        # if current_contract == self.spec_contract:
        #
        #     #spec is always the last one, all its connections are in previous contracts
        #     assert False#len(next_contracts) == 0
        #
        #
        #     for name in output_port_names:
        #         mod = self.spec_out_dict[name]
        #
        #         m_index = model[mod].as_long()
        #         m_mod = self.lib_model.model_by_index(m_index)
        #
        #         m_lev, m_contract = self.lib_model.contract_by_model(m_mod)
        #
        #         # contract shift
        #         # LOG.debug(m_index)
        #         # LOG.debug(shift_map)
        #         m_shift = shift_map[(m_lev, m_contract)]
        #         shifted_ind = self.lib_model.index_shift(m_index, m_shift)
        #
        #         equalities.add(mod == shifted_ind)
        #
        #
        # else:

        current_out_indices = set(self.lib_model.contract_out_indices(current_contract)[current_level])

        # relevant_in_mod = self.lib_model.relevant_input_models(current_level, current_contract)

        # LOG.debug(relevant_in_mod)
        # relevant_in_idx = self.lib_model.relevant_input_indices(current_level, current_contract)
        #
        # relevant_out_mod = self.lib_model.relevant_output_models(current_level, current_contract)
        # relevant_out_idx = self.lib_model.relevant_output_indices(current_level, current_contract)
        # LOG.debug(contract_model_map)
        # shifted_level = (current_level + shift) % self.lib_model.max_components[current_contract]
        for mod in contract_model_map[(current_level, current_contract)]:
            # for mod in relevant_in_mod:

            # LOG.debug(mod)
            # LOG.debug(current_level)
            # LOG.debug(current_contract.base_name)
            shifted_mod = self.lib_model.model_shift(mod, shift)
            m_index = model[mod].as_long()

            if m_index >= self.lib_model.specs_at:
                # this is connected to spec

                s_port_name = self.lib_model.spec_by_index_map[m_index]
                p_type = self.spec.port_type[s_port_name]

                # collect all ports with same type
                # LOG.debug(s_port_name)
                # LOG.debug(self.spec_contract.port_type)
                # LOG.debug(self.spec_contract.out_type_map)
                port_type_class = {x for x in self.spec.in_type_map[p_type]}

                local_eq = set()
                for p_name in port_type_class:
                    # p = self.spec_contract.ports_dict[p_name]
                    p_index = self.lib_model.spec_map[p_name]
                    local_eq.add(shifted_mod == p_index)

                equalities.add(Or(local_eq, self.context))

            else:
                m_mod = self.lib_model.model_by_index(m_index)
                m_lev, m_contract = self.lib_model.contract_by_model(m_mod)

                if (m_lev, m_contract) in previous_contracts:
                    # contract shift
                    # LOG.debug(m_index)
                    # LOG.debug(shift_map)
                    m_shift = shift_map[(m_lev, m_contract)]
                    shifted_ind = self.lib_model.index_shift(m_index, m_shift)

                    # equalities.add(mod == shifted_ind)
                    m_port = self.lib_model.port_by_index(shifted_ind)
                    shifted_level = (m_lev + m_shift) % self.lib_model.max_components[m_contract]
                    p_type = m_contract.port_type[m_port.base_name]

                    # collect all ports with same type
                    port_type_class = {x for x in m_contract.out_type_map[p_type]}

                    local_eq = set()
                    for p_name in port_type_class:
                        p = m_contract.ports_dict[p_name]
                        p_index = self.lib_model.index[p][shifted_level]
                        local_eq.add(shifted_mod == p_index)

                    equalities.add(Or(local_eq, self.context))

                else:
                    # else add to pending
                    if m_index not in pending_equalities:
                        pending_equalities[m_index] = set()
                    pending_equalities[m_index].add(shifted_mod)

        # now all the above models which have indices which are of this contract
        for idx in pending_equalities.keys():
            if idx in current_out_indices:
                mods = pending_equalities[idx]

                shifted_ind = self.lib_model.index_shift(idx, shift)

                m_port = self.lib_model.port_by_index(shifted_ind)
                m_contract = m_port.contract

                shifted_level, _ = self.lib_model.contract_by_index(shifted_ind)

                p_type = m_contract.port_type[m_port.base_name]

                # collect all ports with same type
                port_type_class = {x for x in m_contract.out_type_map[p_type]}

                for mod in mods:
                    # equalities.add(mod == shifted_ind)

                    local_eq = set()
                    for p_name in port_type_class:
                        p = m_contract.ports_dict[p_name]
                        p_index = self.lib_model.index[p][shifted_level]
                        local_eq.add(mod == p_index)

                    equalities.add(Or(local_eq, self.context))

                # reset pending
                pending_equalities.pop(idx)

        # assemble results
        if len(next_contracts) > 0:
            # pick next contract
            (next_lev, next_c) = next_contracts.pop(0)

            inner_shifts = []
            # independent = False
            #
            # if (current_level, current_contract) not in dep_lookup[(next_lev, next_c)]:
            #     independent = True

            for shift in range(self.lib_model.max_components[current_contract]):
                check_dep = [((current_level, current_contract))] + [(l, c) for (l, c) in previous_contracts]
                new_shifts = {(current_level, current_contract): shift}
                new_shifts.update(shift_map)
                pending_eq = {idx: set([x for x in eq_set]) for (idx, eq_set) in pending_equalities.items()}
                next_ctr = [(lev, ctr) for (lev, ctr) in next_contracts]
                prev_ctr = [(lev, ctr) for (lev, ctr) in previous_contracts]

                inner_shifts.append(self.recursive_reject_formula(next_c, next_lev, shift, contract_model_map,
                                                                  model, pending_eq,
                                                                  prev_ctr + [(current_level, current_contract)],
                                                                  next_ctr,
                                                                  new_shifts,
                                                                  output_port_names))
            inner_formula = Or(inner_shifts, self.context)
            # if len(equalities | set([inner_formula])) == 0:
            #     rej_formula = True
            # else:

            rej_formula = And(equalities | set([inner_formula]), self.context)
        else:

            #process spec output ports
            spec_eq = []
            previous_contracts =  previous_contracts + [(current_level, current_contract)]

            for shift in range(self.lib_model.max_components[current_contract]):
                new_shifts = {(current_level, current_contract): shift}
                new_shifts.update(shift_map)

                single_spec_eq = {True}

                for mod in self.spec_outs:
                    m_index = model[mod].as_long()
                    m_mod = self.lib_model.model_by_index(m_index)
                    m_lev, m_contract = self.lib_model.contract_by_model(m_mod)

                    if (m_lev, m_contract) in previous_contracts:
                        # contract shift
                        # LOG.debug(m_index)
                        # LOG.debug(shift_map)
                        m_shift = new_shifts[(m_lev, m_contract)]
                        shifted_ind = self.lib_model.index_shift(m_index, m_shift)

                        # equalities.add(mod == shifted_ind)
                        m_port = self.lib_model.port_by_index(shifted_ind)
                        shifted_level = (m_lev + m_shift) % self.lib_model.max_components[m_contract]
                        p_type = m_contract.port_type[m_port.base_name]

                        # collect all ports with same type
                        port_type_class = {x for x in m_contract.out_type_map[p_type]}

                        local_eq = set()
                        for p_name in port_type_class:
                            p = m_contract.ports_dict[p_name]
                            p_index = self.lib_model.index[p][shifted_level]
                            local_eq.add(mod == p_index)

                        single_spec_eq.add(Or(local_eq, self.context))

                spec_eq.append(And(single_spec_eq, self.context))

            inner_spec_eqs = Or(spec_eq, self.context)

            rej_formula = And(equalities | set([inner_spec_eqs]), self.context)

            # if len(equalities) == 0:
            #     rej_formula = True
            # else:
            #     rej_formula = And(equalities, self.context)

        return rej_formula

    # # def reject_candidate(self, model, failed_spec):
    # def reject_candidate_v0(self, model, output_port_names):
    #     '''
    #     reject a model and its equivalents
    #     '''
    #     # LOG.debug('IN')
    #
    #     #get only relevant models, i.e., connected eventually to the spec
    #     models, spec_models = self.__infer_relevant_ports_from_model(model, output_port_names)
    #     # now we get all the contracts related to the models.
    #     # by construction fetching only the outputs, we have the full set of contracts
    #     model_map, contract_map = self.lib_model.contract_copies_by_models(models)
    #
    #     # LOG.debug('mid')
    #
    #     # tim = time.time()
    #
    #
    #     #get the spec details. Only one component connected to spec
    #
    #     spec_port_models = [self.spec_out_dict[name] for name in output_port_names]
    #     spec_idx = {mod.get_id(): model[mod].as_long() for mod in spec_port_models}
    #     mods = {mod.get_id(): self.lib_model.models[spec_idx[mod.get_id()]]
    #             for mod in spec_port_models}
    #
    #     spec_connections = {}
    #     for sid, mod in mods.items():
    #         (level, contract) = self.lib_model.contract_by_model(mod)
    #         spec_connections[sid] = (level, contract)
    #
    #     comp_list_size = len(contract_map.values())
    #
    #     level_map = itertools.product(range(self.lib_model.max_components), repeat=comp_list_size)
    #     contract_shift_pos = {(lev, contract): contract_map.keys().index((lev, contract))
    #                            for lev, contract in contract_map.keys()}
    #
    #     contract_models = {contract:self.lib_model.contract_in_models(contract)
    #                        for _, contract in contract_map.keys()}
    #
    #     contract_idx = {contract:self.lib_model.contract_indices(contract)
    #                        for _, contract in contract_map.keys()}
    #
    #     constraints = []
    #
    #     for level_shift in level_map:
    #
    #         conj = []
    #
    #         #spec port --
    #         for spec_mod in spec_port_models:
    #             level, contract = spec_connections[spec_mod.get_id()]
    #
    #             idx_shift = level_shift[contract_shift_pos[(level, contract)]]
    #             spec_new_idx = self.lib_model.index_shift(spec_idx[spec_mod.get_id()], idx_shift)
    #
    #             conj.append(spec_mod == spec_new_idx)
    #
    #         for mod in models:
    #             if model[mod] is not None:
    #                 (model_level, model_contract) = self.lib_model.contract_by_model(mod)
    #
    #                 try:
    #                     connected_model = self.lib_model.model_by_index(model[mod].as_long())
    #                 except IndexError:
    #                     connected_model = None
    #                     idx_contract = None
    #                 else:
    #                     (idx_level, idx_contract) = self.lib_model.contract_by_model(connected_model)
    #
    #                 shift = level_shift[contract_shift_pos[(model_level, model_contract)]]
    #
    #                 new_mod = self.lib_model.model_shift(mod, shift)
    #
    #                 if connected_model is None:
    #                     #in this case port is connected to spec port
    #                     #idx_shift = 0
    #                     new_idx = model[mod].as_long()
    #                 else:
    #
    #                     idx_shift = level_shift[contract_shift_pos[(idx_level, idx_contract)]]
    #                     new_idx = self.lib_model.index_shift(model[mod].as_long(), idx_shift)
    #
    #                 conj.append(new_mod == new_idx)
    #
    #         constraints.append(And(conj, self.context))
    #
    #     rej_formula = Not(Or(constraints, self.context), self.context)
    #
    #     # LOG.debug('inner done')
    #
    #     self.solver.add(rej_formula)
    #
    #     # LOG.debug(time.time()-tim)
    #
    #     return None
    #
    # def reject_candidate_v1(self, model, output_port_names):
    #     '''
    #     reject a model and its equivalents
    #     '''
    #     # LOG.debug('IN')
    #
    #     #get only relevant models, i.e., connected eventually to the spec
    #     models, spec_models = self.__infer_relevant_ports_from_model(model, output_port_names)
    #     # now we get all the contracts related to the models.
    #     # by construction fetching only the outputs, we have the full set of contracts
    #     model_map, contract_map = self.lib_model.contract_copies_by_models(models)
    #
    #     # level_contracts_pairs = set(contract_map.keys())
    #
    #     # infer contract dependency
    #     c_dep = self.__infer_contract_dependency(model, output_port_names)
    #
    #     next_contracts_unordered = contract_map.keys()
    #
    #     next_contracts_unorderedracts = next_contracts_unordered
    #     next_contracts = []
    #
    #     # LOG.debug(c_dep)
    #
    #     if len(c_dep) > 0:
    #         #the initial element is the one with fewer dependencies
    #         next_contracts = [min(c_dep.keys(), key=lambda x: len(c_dep[x]))]
    #     # else:
    #     #     next_contracts = contract_map.keys()
    #     #
    #     # LOG.debug(next_contracts_unordered)
    #     # LOG.debug(contract_map)
    #
    #     # next_contracts = [next_contracts_unordered[0]]
    #     # LOG.debug(next_contracts)
    #     while len(next_contracts) != len(next_contracts_unordered):
    #         for (l1, c1) in next_contracts_unordered:
    #
    #             if (l1, c1) not in next_contracts:
    #                 # LOG.debug((l1,c1))
    #                 # LOG.debug(next_contracts)
    #                 if all([x in next_contracts for x in c_dep[(l1,c1)]]):
    #                     next_contracts.append((l1,c1))
    #                     # LOG.debug(next_contracts)
    #                     break
    #
    #     # LOG.debug(next_contracts)
    #     # assert False
    #
    #
    #
    #
    #     # LOG.debug(model)
    #     # LOG.debug(models)
    #     # LOG.debug(spec_models)
    #     # LOG.debug(model_map)
    #     # LOG.debug(contract_map)
    #
    #
    #
    #
    #     # chain_c_dep = {(lev, contract): {} for lev, contract in next_contracts}
    #
    #     # for i in range(len(next_contracts)):
    #     #     (lev, contract) = next_contracts[i]
    #     #     chain_c_dep[(lev, contract)][frozenset([next_contracts[j]
    #     #         for j in range(i+1, len(next_contracts))])] = [next_contracts[j] for j in range(i+1, len(next_contracts))
    #
    #
    #     contract_model_map = {}
    #     for (current_level, current_contract) in next_contracts:
    #         # contract_model_map[(current_level, current_contract)] = self.lib_model.contract_in_models(current_contract)[current_level]
    #         contract_model_map[(current_level, current_contract)] = self.lib_model.relevant_input_models(current_level, current_contract)
    #
    #
    #     #first contract
    #     current_lev, current_contract = next_contracts.pop(0)
    #     #add spec
    #     # next_contracts.append((0, self.spec_contract))
    #     inner_shifts = []
    #     # LOG.debug(next_contracts)
    #
    #     pending_equalities = {}
    #     for name in output_port_names:
    #         mod = self.spec_out_dict[name]
    #
    #         m_index = model[mod].as_long()
    #
    #         if m_index not in pending_equalities:
    #             pending_equalities[m_index] = set()
    #         pending_equalities[m_index].add(mod)
    #
    #
    #     # #figure out reusable chunks
    #     #     dep_lookup = {}
    #     # for i in range(len(next_contracts)):
    #     #     l, c = next_contracts[i]
    #     #     dep_set = set()
    #     #
    #     #     for j in range(i, len(next_contracts)):
    #     #         for x in c_dep[next_contracts[j]]:
    #     #             dep_set.add(x)
    #     #
    #     #     dep_lookup[(l, c)] = dep_set
    #     #     formula_lookup = {}
    #
    #
    #     # LOG.debug('mid')
    #
    #     tim = time.time()
    #
    #     pool = []
    #     res_queue = Queue()
    #
    #     for shift in range(self.lib_model.max_components):
    #         previous_contracts = []
    #         pending_eq = {idx: set([x for x in eq_set]) for (idx, eq_set) in pending_equalities.items()}
    #         next_c_iter = [(lev, contract) for (lev, contract) in next_contracts]
    #         new_shifts = {(current_lev, current_contract): shift}
    #         # inner_shifts.append(self.recursive_reject_formula(current_contract, current_lev, shift,
    #         #                                                   contract_model_map,
    #         #                                                   model, pending_eq,
    #         #                                                   previous_contracts, next_c_iter,
    #         #                                                   new_shifts, output_port_names))
    #
    #         solv = RejectProcess(current_contract, current_lev, shift, contract_model_map,
    #                              model, pending_eq,
    #                              previous_contracts,
    #                              next_c_iter,
    #                                 new_shifts, output_port_names,
    #                                 self, res_queue)
    #
    #         solv.start()
    #         pool.append(solv)
    #
    #     # LOG.debug('started')
    #     for p in pool:
    #         p.join()
    #
    #     # LOG.debug('inner done')
    #     # inner_shifts = []
    #     while not res_queue.empty():
    #         r = res_queue.get_nowait()
    #         # LOG.debug(r)
    #         inner_shifts.append(r)
    #
    #     # inner_formula = Or(inner_shifts, self.context)
    #     # # LOG.debug(Not(inner_formula))
    #     # # LOG.debug(len(Not(inner_formula).__repr__()))
    #     #
    #     # rej = Not(inner_formula, self.context)
    #     # self.solver.add(rej)
    #
    #     inner_str = ' '.join(inner_shifts)
    #     decl_str = '\n'.join(self.lib_model.int_decl)
    #     rej_string = '%s (assert (not (or %s)))' % (decl_str, inner_str)
    #     # LOG.debug(rej_string)
    #     inner_formula = parse_smt2_string(rej_string,
    #                                               ctx=self.context)
    #
    #
    #     # LOG.debug(time.time()-tim)
    #     return None


    # def reject_candidate(self, model, failed_spec):
    def reject_candidate(self, model, output_port_names):
        '''
        reject a model and its equivalents
        '''
        # LOG.debug('IN')

        #get only relevant models, i.e., connected eventually to the spec
        models, spec_models = self._infer_relevant_ports_from_model(model, output_port_names)
        # now we get all the contracts related to the models.
        # by construction fetching only the outputs, we have the full set of contracts
        model_map, contract_map = self.lib_model.contract_copies_by_models(models)

        # level_contracts_pairs = set(contract_map.keys())

        # infer contract dependency
        c_dep = self.__infer_contract_dependency(model, output_port_names)

        next_contracts_unordered = contract_map.keys()

        next_contracts = []

        # LOG.debug(c_dep)

        if len(c_dep) > 0:
            #the initial element is the one with fewer dependencies
            next_contracts = [min(c_dep.keys(), key=lambda x: len(c_dep[x]))]
        # else:
        #     next_contracts = contract_map.keys()
        #
        # LOG.debug(next_contracts_unordered)
        # LOG.debug(contract_map)

        # next_contracts = [next_contracts_unordered[0]]
        # LOG.debug(next_contracts)
        while len(next_contracts) != len(next_contracts_unordered):
            for (l1, c1) in next_contracts_unordered:

                if (l1, c1) not in next_contracts:
                    # LOG.debug((l1,c1))
                    # LOG.debug(next_contracts)
                    if all([x in next_contracts for x in c_dep[(l1,c1)]]):
                        next_contracts.append((l1,c1))
                        # LOG.debug(next_contracts)
                        break

        # LOG.debug(next_contracts)
        # assert False




        # LOG.debug(model)
        # LOG.debug(models)
        # LOG.debug(spec_models)
        # LOG.debug(model_map)
        # LOG.debug(contract_map)




        # chain_c_dep = {(lev, contract): {} for lev, contract in next_contracts}

        # for i in range(len(next_contracts)):
        #     (lev, contract) = next_contracts[i]
        #     chain_c_dep[(lev, contract)][frozenset([next_contracts[j]
        #         for j in range(i+1, len(next_contracts))])] = [next_contracts[j] for j in range(i+1, len(next_contracts))


        contract_model_map = {}
        for (current_level, current_contract) in next_contracts:
            # contract_model_map[(current_level, current_contract)] = self.lib_model.contract_in_models(current_contract)[current_level]
            contract_model_map[(current_level, current_contract)] = self.lib_model.relevant_input_models(current_level, current_contract)


        #first contract
        current_lev, current_contract = next_contracts.pop(0)
        #add spec
        # next_contracts.append((0, self.spec_contract))
        inner_shifts = []
        # LOG.debug(next_contracts)

        pending_equalities = {}
        for name in output_port_names:
            mod = self.spec_out_dict[name]

            m_index = model[mod].as_long()

            if m_index not in pending_equalities:
                pending_equalities[m_index] = set()
            pending_equalities[m_index].add(mod)


        # #figure out reusable chunks
        #     dep_lookup = {}
        # for i in range(len(next_contracts)):
        #     l, c = next_contracts[i]
        #     dep_set = set()
        #
        #     for j in range(i, len(next_contracts)):
        #         for x in c_dep[next_contracts[j]]:
        #             dep_set.add(x)
        #
        #     dep_lookup[(l, c)] = dep_set
        #     formula_lookup = {}


        # LOG.debug('mid')

        # tim = time.time()

        pool = []
        res_queue = Queue()
        # LOG.debug(output_port_names)
        for shift in range(self.lib_model.max_components[current_contract]):
            previous_contracts = []
            pending_eq = {idx: set([x for x in eq_set]) for (idx, eq_set) in pending_equalities.items()}
            next_c_iter = [(lev, contract) for (lev, contract) in next_contracts]
            new_shifts = {(current_lev, current_contract): shift}
            inner_shifts.append(self.recursive_reject_formula(current_contract, current_lev, shift,
                                                              contract_model_map,
                                                              model, pending_eq,
                                                              previous_contracts, next_c_iter,
                                                              new_shifts, output_port_names))

        #     solv = RejectProcess(current_contract, current_lev, shift, contract_model_map,
        #                          model, pending_eq,
        #                          previous_contracts,
        #                          next_c_iter,
        #                             new_shifts, output_port_names,
        #                             self, res_queue)
        #
        #     solv.start()
        #     pool.append(solv)
        #
        # LOG.debug('started')
        # for p in pool:
        #     p.join()
        #
        # LOG.debug('inner done')
        # # inner_shifts = []
        # while not res_queue.empty():
        #     r = res_queue.get_nowait()
        #     # LOG.debug(r)
        #     inner_shifts.append(r)
        #
        # inner_str = ' '.join(inner_shifts)
        # decl_str = '\n'.join(self.lib_model.int_decl)
        # rej_string = '%s (assert (not (or %s)))' % (decl_str, inner_str)
        # # LOG.debug(rej_string)
        # inner_formula = parse_smt2_string(rej_string,
        #                                           ctx=self.context)
        # LOG.debug('inner done')
        inner_formula = Or(inner_shifts, self.context)
        # LOG.debug(Not(inner_formula))
        # LOG.debug(len(Not(inner_formula).__repr__()))

        rej = Not(inner_formula, self.context)
        # LOG.debug(rej)
        # other = self.reject_candidate_v0(model, output_port_names)

        # z3.prove(other)
        #
        goal = Tactic('simplify', ctx=self.context)
        # goal.add(rej)
        goal = goal.apply(rej)

        self.solver.add(goal.as_expr())

        # LOG.debug(time.time()-tim)
        return None





        # #get the spec details. Only one component connected to spec
        #
        # spec_port_models = [self.spec_out_dict[name] for name in output_port_names]
        # spec_idx = {mod.get_id(): model[mod].as_long() for mod in spec_port_models}
        # mods = {mod.get_id(): self.lib_model.models[spec_idx[mod.get_id()]]
        #         for mod in spec_port_models}
        #
        # spec_connections = {}
        # for sid, mod in mods.items():
        #     (level, contract) = self.lib_model.contract_by_model(mod)
        #     spec_connections[sid] = (level, contract)
        #
        # comp_list_size = len(contract_map.values())
        #
        # level_map = itertools.product(range(self.lib_model.max_components), repeat=comp_list_size)
        # contract_shift_pos = {(lev, contract): contract_map.keys().index((lev, contract))
        #                        for lev, contract in contract_map.keys()}
        #
        # contract_models = {contract:self.lib_model.contract_in_models(contract)
        #                    for _, contract in contract_map.keys()}
        #
        # contract_idx = {contract:self.lib_model.contract_indices(contract)
        #                    for _, contract in contract_map.keys()}
        #
        # constraints = []
        #
        # for level_shift in level_map:
        #
        #     conj = []
        #
        #     #spec port --
        #     for spec_mod in spec_port_models:
        #         level, contract = spec_connections[spec_mod.get_id()]
        #
        #         idx_shift = level_shift[contract_shift_pos[(level, contract)]]
        #         spec_new_idx = self.lib_model.index_shift(spec_idx[spec_mod.get_id()], idx_shift)
        #
        #         conj.append(spec_mod == spec_new_idx)
        #
        #     for mod in models:
        #         if model[mod] is not None:
        #             (model_level, model_contract) = self.lib_model.contract_by_model(mod)
        #
        #             if model in self.lib_model.relevant_input_models(model_level, model_contract):
        #                 try:
        #                     connected_model = self.lib_model.model_by_index(model[mod].as_long())
        #                 except IndexError:
        #                     connected_model = None
        #                     idx_contract = None
        #                 else:
        #                     (idx_level, idx_contract) = self.lib_model.contract_by_model(connected_model)
        #
        #                 shift = level_shift[contract_shift_pos[(model_level, model_contract)]]
        #
        #                 new_mod = self.lib_model.model_shift(mod, shift)
        #
        #                 if connected_model is None:
        #                     #in this case port is connected to spec port
        #                     #idx_shift = 0
        #                     new_idx = model[mod].as_long()
        #                 else:
        #
        #                     idx_shift = level_shift[contract_shift_pos[(idx_level, idx_contract)]]
        #                     new_idx = self.lib_model.index_shift(model[mod].as_long(), idx_shift)
        #
        #                 conj.append(new_mod == new_idx)
        #
        #     constraints.append(And(conj, self.context))
        #
        # rej_formula = Not(Or(constraints, self.context), self.context)
        # LOG.debug('inner done')
        #
        # self.solver.add(rej_formula)
        #
        # LOG.debug(time.time()-tim)
        #
        # return rej_formula


        # c_sets = {}
        #
        #
        # for spec in self.spec_outs:
        #     index = model[spec].as_long()
        #     mod = self.lib_model.models[index]
        #     (level, contract) = self.lib_model.contract_by_model(mod)
        #     if (level, contract) not in c_sets:
        #         c_sets[(level, contract)] = {}
        #         # find all related models
        #         # in_models = self.lib_model.related_in_models(mod)
        #         # for mod in in_models:
        #         #    c_sets[(level, contract)][mod.get_id()] = (mod, model[mod].as_long())
        #
        #     c_sets[(level, contract)][spec.get_id()] = (spec, index)
        #
        # size = len(c_sets)
        #
        # # create containers as nested lists
        # # one per each c_set and n lists inside
        # classes = []
        #
        # for (level, contract) in c_sets:
        #     s_class = []
        #     s_pairs = c_sets[(level, contract)].values()
        #     mods = self.lib_model.contract_in_models(contract)
        #
        #     for l in xrange(0, self.lib_model.max_components):
        #         l_class = []
        #         shift = self.lib_model.max_components - level + l
        #         for pair in s_pairs:
        #             if pair[0].get_id() not in self.dummy_model_set:
        #                 l_class.append([pair[0] == self.lib_model.index_shift(pair[1], shift)])
        #         for i in xrange(0, len(mods[l])):
        #             m_class = []
        #             if model[mods[level][i]].as_long() < self.lib_model.max_index:
        #                 for l2 in xrange(0, self.lib_model.max_components):
        #                     shift = self.lib_model.max_components - level + l2
        #                     m_class.append(mods[l][i] ==
        #                                    self.lib_model.index_shift(model[mods[level][i]].as_long(), shift))
        #             else:
        #                 m_class.append(mods[l][i] == model[mods[level][i]].as_long())
        #
        #             l_class.append(m_class)
        #         s_class.append(l_class)
        #     classes.append(s_class)
        #
        # # size
        #
        #
        # rej_formula = Not(
        #     And(
        #         [Or(
        #             [And(
        #                 [Or(
        #                     [And(line) for line in m_class]
        #                 )
        #                  for m_class in l_class]
        #             )
        #              for l_class in s_class]
        #         )
        #          for s_class in classes]
        #     )
        # )
        #
        # # LOG.debug(rej_formula)
        #
        # # self.solver.add(rej_formula)
        # return rej_formula

# class RejectProcess(Process):
#     '''
#     process processing part of the reject formula
#     '''
#
#     def __init__(self, current_contract, current_level, shift,
#                                  contract_model_map, model,
#                                  pending_equalities,
#                                  previous_contracts, next_contracts,
#                                  shift_map, output_port_names,
#                                  manager, res_queue):
#
#         self.current_contract = current_contract
#         self.current_level = current_level
#         self.shift = shift
#         self.contract_model_map = contract_model_map
#         self.model = model
#         self.pending_equalities = pending_equalities
#         self.previous_contracts = previous_contracts
#         self.next_contracts = next_contracts
#         self.shift_map = shift_map
#         self.output_port_names = output_port_names
#         self.res_queue = res_queue
#         self.manager = manager
#
#         super(RejectProcess, self).__init__()
#
#
#     def run(self):
#         '''
#         run the process
#         :return:
#         '''
#
#         equalities = set()
#
#
#         current_out_indices = self.manager.lib_model.contract_out_indices(self.current_contract)[self.current_level]
#
#
#         for mod in self.contract_model_map[(self.current_level, self.current_contract)]:
#         # for mod in relevant_in_mod:
#
#             # LOG.debug(mod)
#             # LOG.debug(current_level)
#             # LOG.debug(current_contract.base_name)
#             m_index = self.model[mod].as_long()
#
#
#             if m_index >= self.manager.lib_model.specs_at:
#                 #this is connected to spec
#                 equalities.add(mod == m_index)
#             else:
#                 m_mod = self.manager.lib_model.model_by_index(m_index)
#                 m_lev, m_contract = self.manager.lib_model.contract_by_model(m_mod)
#
#                 if (m_lev, m_contract) in self.previous_contracts:
#                     # contract shift
#                     # LOG.debug(m_index)
#                     # LOG.debug(shift_map)
#                     m_shift = self.shift_map[(m_lev, m_contract)]
#                     shifted_ind = self.manager.lib_model.index_shift(m_index, m_shift)
#
#                     equalities.add(mod == shifted_ind)
#
#                 else:
#                     #else add to pending
#                     if m_index not in self.pending_equalities:
#                         self.pending_equalities[m_index] = set()
#
#                     self.pending_equalities[m_index].add(mod)
#
#
#         #now all the above models which have indices which are of this contract
#         for idx in current_out_indices:
#             if idx in self.pending_equalities:
#                 mods = self.pending_equalities[idx]
#
#                 shifted_ind = self.manager.lib_model.index_shift(idx, self.shift)
#
#                 for mod in mods:
#                     equalities.add(mod == shifted_ind)
#
#                 # reset pending
#                 self.pending_equalities.pop(idx)
#
#
#         #assemble results
#         if len(self.next_contracts) > 0:
#             #pick next contract
#             (next_lev, next_c) = self.next_contracts.pop(0)
#
#             inner_shifts = []
#
#
#             pool = []
#             inner_queue = Queue()
#
#
#             for l_shift in range(self.manager.lib_model.max_components):
#
#                 # check_dep = [((self.current_level, self.current_contract))]+[(l,c) for (l,c) in self.previous_contracts]
#                 new_shifts = {(self.current_level, self.current_contract): l_shift}
#                 new_shifts.update(self.shift_map)
#                 pending_eq = {idx: set([x for x in eq_set]) for (idx, eq_set) in self.pending_equalities.items()}
#                 next_ctr = [(lev, ctr) for (lev, ctr) in self.next_contracts]
#                 prev_ctr = [(lev, ctr) for (lev, ctr) in self.previous_contracts]
#
#                 inner_shifts.append(self.manager.recursive_reject_formula(next_c, next_lev, self.shift, self.contract_model_map,
#                                                                       self.model, pending_eq,
#                                                                       prev_ctr + [(self.current_level, self.current_contract)],
#                                                                       next_ctr,
#                                                                       new_shifts, self.output_port_names))
#
#             inner_formula = Or(inner_shifts, self.manager.context)
#             # if len(equalities | set([inner_formula])) == 0:
#             #     rej_formula = True
#             # else:
#
#             rej_formula = And(equalities | {inner_formula}, self.manager.context)
#         else:
#             if len(equalities) == 0:
#                 rej_formula = True#BoolVal(True, self.manager.context)
#             else:
#                 rej_formula = And(equalities, self.manager.context)
#
#         # LOG.debug(rej_formula.range())
#         # goal = Goal(ctx=self.manager.context)
#         # goal.add(rej_formula)
#         t = Tactic('simplify', ctx=self.manager.context)
#         goal = t.apply(rej_formula)
#         self.res_queue.put(goal.as_expr().sexpr())
#         # return rej_formula





class NotSynthesizableError(Exception):
    '''
    raised if it is not possible to synthesize a controller
    '''
    pass

class OptimizationError(Exception):
    '''
    raised if it is not possible to synthesize a controller
    '''
    pass