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

# MAX_SOLVERS = 10

class SinglePortSolver(multiprocessing.Process):
    '''
    this process synthesizes a solution for a single output port
    '''

    def __init__(self, z3_interface, assertions,
                 context,
                 spec_port_name, spec_contract, library_max_redundancy, limit,
                 minimize_components=False, minimize_ports=False):

        self.z3_interface = z3_interface

        self.spec_contract = spec_contract
        self.context = context
        self.assertions = assertions
        self.spec_port_name = spec_port_name
        # self.lib_model = self.z3_interface.lib_model
        # self.spec_out_dict = {name: mod.translate(self.context) for (name, mod) in
        #                       self.z3_interface.spec_out_dict.items()}

        # self.spec_out_dict = self.z3_interface.spec_out_dict

        self.spec_out_dict = {name: z3.Int('%s' % name, self.context) for name
                              in self.spec_contract.output_ports_dict}
        self.spec_in_dict = {name: z3.Int('%s' % name, self.context) for name
                             in self.spec_contract.input_ports_dict}

        self.spec_dict = dict(self.spec_in_dict.items() + self.spec_out_dict.items())

        self.spec_outs = self.spec_out_dict.values()
        self.spec_ins = self.spec_in_dict.values()

        self.num_out = len(self.spec_outs)

        self.lib_model = Z3Library(self.z3_interface.library, self.spec_contract,
                                   library_max_redundancy=library_max_redundancy, limit=limit,
                                   context=self.context)
        self.lib_model.include_spec_ports(self.spec_contract)


        self.specification_list = self.z3_interface.specification_list
        self.dummy_model_set = self.z3_interface.dummy_model_set


        # r = t.apply(self.goal_constraints)
        #
        optimize = minimize_components or minimize_ports

        self.solver = Solver(ctx=self.context)
        if optimize:
            self.solver = Optimize(ctx=self.context)

        self.solver.add(self.assertions)

        super(SinglePortSolver, self).__init__()


    def run(self):


        initial_size = self.z3_interface.max_components

        size = initial_size
        if MAX_THREADS >= 1:
            thread_manager = ModelVerificationManager(self, self.spec_port_name)

            try:
                (model, composition,
                 spec, contract_list) = thread_manager.synthesize()
            except NotSynthesizableError:
                raise
            else:
                LOG.info(model)
                for c in contract_list:
                    LOG.debug(c)
                LOG.info(spec)
                LOG.info(composition)
                from graphviz_converter import GraphizConverter
                graphviz_conv = GraphizConverter(spec, composition, contract_list, filename=self.spec_port_name)
                graphviz_conv.generate_graphviz()
                graphviz_conv.view()
                return model, composition, spec, contract_list

                # return model, composition, spec, contract_list
        else:
            while True:
                try:
                    model = self.propose_candidate()
                except NotSynthesizableError as err:
                    raise err
                else:
                    try:
                        composition, spec, contract_list = self.verify_candidate(model, self.spec_port_name)
                    except NotSynthesizableError as err:
                        LOG.debug("candidate not valid")
                    else:
                        LOG.info(model)
                        for c in contract_list:
                            LOG.debug(c)
                        LOG.info(self.spec_contract)
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
        #LOG.debug(self.solver.lower(self.obj))
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

    def check_all_specs(self, model, output_port_name):
        '''
        check if the model satisfies a number of specs, if provided
        :param output_port_name:
        '''
        composition = None
        connected_spec = None
        contract_inst = None
        failed_spec = None
        for spec in self.specification_list:
            composition, connected_spec, contract_inst = \
                self.build_composition_from_model(model, spec, output_port_name)

            if not composition.is_refinement(connected_spec):
                LOG.debug('ref check done 1')
                failed_spec = spec
                return False, composition, connected_spec, contract_inst, failed_spec

            LOG.debug('ref check done 2')

        return True, composition, connected_spec, contract_inst, None


    def __infer_relevant_ports_from_model(self, model, output_port_name):
        '''
        Create a list of contracts connected to the spec, eliminating spurious results

        :param model:
        :param spec:
        :param output_port_name:
        :return:
        '''

        # now we need to collect all the components connected in chain to the spec output we are considering
        # we start with the model connected to the out
        spec_port_model = self.spec_out_dict[output_port_name]
        models = []

        to_process = [self.lib_model.model_by_index(model[spec_port_model].as_long())]
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

            # add for further processing
            for mod in connected_models:
                if mod not in done:
                    to_process.append(mod)

        return models, spec_models

    def build_composition_from_model(self, model, spec, output_port_name):
        '''
        builds a contract composition out of a model
        :param output_port_name:
        '''

        # contracts = set()
        spec_contract = spec.copy()
        working_spec = spec.copy()

        # LOG.debug(spec_contract)

        # find all contracts from model
        # a set will help us remove duplicates
        # contracts = set()

        #now we need to collect all the components connected in chain to the spec output we are considering
        # we start with the model connected to the out
        spec_port_model = self.spec_out_dict[output_port_name]

        # LOG.debug(model)
        # LOG.debug(output_port_name)

        models, spec_models = self.__infer_relevant_ports_from_model(model, output_port_name)
        #
        # LOG.debug(models)
        # LOG.debug(spec_models)

        # now we get all the contracts related to the models.
        # by construction fetching only the outputs, we have the full set of contracts
        model_map, contract_map = self.lib_model.contract_copies_by_models(models)
        #
        # LOG.debug(model)
        # LOG.debug(model_map)
        # LOG.debug(contract_map)

        contracts = set(model_map.values())
        # contracts.add(working_spec)
        # extended_contracts = dict(list(contracts) + [spec_contract])

        # start composition
        # c_set = contracts
        # c_set.add(contracts.values()[0])
        mapping = CompositionMapping(contracts| set([working_spec]))

        #process working spec
        for port in working_spec.ports_dict.values():
            name = port.base_name

            if name != output_port_name:
                spec_contract.connect_to_port(spec_contract.ports_dict[name], port)

        # start with spec port
        # TODO: maybe remove these checks
        if model[spec_port_model].as_long() != -1:
            if spec_port_model.get_id() not in self.dummy_model_set:
                #there might be dummie ports

                name = str(spec_port_model)
                spec_port = spec_contract.ports_dict[name]

                index = model[spec_port_model].as_long()
                i_mod = self.lib_model.models[index]
                level = self.lib_model.model_levels[i_mod.get_id()]
                orig_port = self.lib_model.port_by_index(index)

                other_contract_orig = orig_port.contract
                other_contract = contract_map[(level, other_contract_orig)]

                port = other_contract.ports_dict[orig_port.base_name]

                spec_contract.connect_to_port(spec_port, port)

        # connections among candidates
        processed_ports = set()
        for p_model in models + spec_models:
            level, old_contract = self.lib_model.contract_by_model(p_model)
            current_contract = contract_map[(level, old_contract)]
            old_port = self.lib_model.port_by_model(p_model)
            current_port = current_contract.ports_dict[old_port.base_name]
            other_index = model[p_model].as_long()

            if other_index < self.lib_model.specs_at:

                other_mod = self.lib_model.models[other_index]
                other_level = self.lib_model.model_levels[other_mod.get_id()]

                other_port_orig = self.lib_model.port_by_index(other_index)

                other_contract = contract_map[(other_level, other_port_orig.contract)]

                other_port = other_contract.ports_dict[other_port_orig.base_name]

                mapping.connect(current_port, other_port,
                                '%s_%s' % (current_contract.unique_name,
                                           current_port.base_name))

                # LOG.debug(current_contract.unique_name)
                # LOG.debug(other_contract.unique_name)
                # LOG.debug(current_port.unique_name)
                # LOG.debug(other_port.unique_name)
                processed_ports.add(current_port)
                processed_ports.add(other_port)

            else:
                spec_port = spec_contract.ports_dict[self.lib_model.spec_by_index_map[other_index]]

                if spec_port.is_input:
                    spec_contract.connect_to_port(spec_port, current_port)
                else:
                    working_spec.connect_to_port(working_spec.ports_dict[spec_port.base_name], current_port)


        # add all the remaining names to new composition
        for (level, old_contract) in contract_map.keys():
            for old_port in old_contract.ports_dict.values():
                current_contract = contract_map[(level, old_contract)]
                current_port = current_contract.ports_dict[old_port.base_name]
                if current_port not in processed_ports:
                    mapping.add(current_port, '%s_%s' % (current_contract.unique_name,
                                                         current_port.base_name))
                    processed_ports.add(current_port)

        # for contract in contracts:
        #    LOG.debug(contract)
        # LOG.debug(spec_contract)

        # if not complete_model:
        #    c_set = self.filter_candidate_contracts_for_composition(contracts, spec_contract)

        # compose
        #root = contracts.pop()

        # c_set.add(root.copy())

        composition = working_spec.compose(contracts, composition_mapping=mapping)

        # LOG.debug('-----------')
        # LOG.debug(model)
        # LOG.debug(working_spec)
        # for contract in contracts:
        #    LOG.debug(contract)
        #
        # LOG.debug(composition)
        # LOG.debug(spec_contract)
        #
        #
        #
        # from graphviz_converter import GraphizConverter
        # graphviz_conv = GraphizConverter(spec_contract, composition, contracts | set([working_spec]))
        # graphviz_conv.generate_graphviz()
        # graphviz_conv.view()

        # LOG.debug('done')
        return composition, spec_contract, contracts


    # def assemble_reject_formula(self, component, connection_dict):
    #     '''
    #     recursively assemble the formula for the rejected model
    #     :param component:
    #     :param connection_dict:
    #     :return:
    #     '''
    #
    #     #base case
    #     if connection_dict[component] == []:
    #


    # def reject_candidate(self, model, failed_spec):
    def reject_candidate(self, model, output_port_name):
        '''
        reject a model and its equivalents
        '''

        #get only relevant models, i.e., connected eventually to the spec
        models, spec_models = self.__infer_relevant_ports_from_model(model, output_port_name)
        # now we get all the contracts related to the models.
        # by construction fetching only the outputs, we have the full set of contracts
        model_map, contract_map = self.lib_model.contract_copies_by_models(models)

        level_contracts_pairs = set(contract_map.keys())

        # LOG.debug(models)
        # LOG.debug(spec_models)
        # LOG.debug(model_map)
        # LOG.debug(contract_map)


        #get the spec details. Only one component connected to spec

        spec_port_model = self.spec_out_dict[output_port_name]
        index = model[spec_port_model].as_long()
        mod = self.lib_model.models[index]
        (level, contract) = self.lib_model.contract_by_model(mod)

        comp_list_size = len(contract_map.values())

        level_map = itertools.product(range(self.lib_model.max_components), repeat=comp_list_size)
        contract_shift_pos = {(lev, contract): contract_map.keys().index((lev, contract))
                               for lev, contract in contract_map.keys()}

        contract_models = {contract:self.lib_model.contract_in_models(contract)
                           for _, contract in contract_map.keys()}

        contract_idx = {contract:self.lib_model.contract_indices(contract)
                           for _, contract in contract_map.keys()}

        constraints = []

        for level_shift in level_map:

            conj = []

            #and spec -- out of for loop
            idx_shift = level_shift[contract_shift_pos[(level, contract)]]
            spec_new_idx = self.lib_model.index_shift(index, idx_shift)
            conj.append(spec_port_model == spec_new_idx)

            for mod in models:
                (model_level, model_contract) = self.lib_model.contract_by_model(mod)

                try:
                    connected_model = self.lib_model.model_by_index(model[mod].as_long())
                except IndexError:
                    connected_model = None
                    idx_contract = None
                else:
                    (idx_level, idx_contract) = self.lib_model.contract_by_model(connected_model)

                shift = level_shift[contract_shift_pos[(model_level, model_contract)]]

                new_mod = self.lib_model.model_shift(mod, shift)

                if connected_model is None:
                    #in this case port is connected to spec port
                    idx_shift = 0
                else:
                    print contract_shift_pos
                    idx_shift = level_shift[contract_shift_pos[(idx_level, idx_contract)]]

                new_idx = self.lib_model.index_shift(model[mod].as_long(), idx_shift)

                conj.append(new_mod == new_idx)

            constraints.append(And(conj, self.context))

        rej_formula = Not(Or(constraints, self.context), self.context)
        # LOG.debug(rej_formula)
        return rej_formula


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