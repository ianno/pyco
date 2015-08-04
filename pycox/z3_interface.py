'''
This module includes the interface classes and functions for the Z3 SMT solver

Author: Antonio Iannopollo
'''

#import logging
from pycox import LOG
from pycox.smt_factory import SMTModelFactory
from z3 import *
import itertools
import types
from pycox.contract import CompositionMapping, RefinementMapping
from time import time

#LOG = logging.getLogger()
LOG.debug('in z3_interface')


class Z3Library(object):
    '''
    maps library to a set of integers
    '''

    def __init__(self, library, spec):
        '''
        associate library and create models.
        We need the spec, too, because we need to determine
        the number of replicate components we need.
        TODO
        There is a problem with the size of the library, though...
        '''
        self.library = library
        self.models = []
        self.ports = []
        self.index = {}
        self.model_index = {}
        self.model_in_index = {}
        self.model_out_index = {}
        self.contract_index = {}
        self.out_models = []
        self.out_ports = []
        self.out_index = {}
        self.out_contract_index = {}
        self.in_models = []
        self.in_ports = []
        self.in_index = {}
        self.in_contract_index = {}
        self.model_levels = {}
        self.model_contracts = {}
        self.contracts = set()

        self.spec = spec
        self.max_components = len(spec.output_ports_dict)

        for level in range(0, self.max_components):
            self.contract_index[level] = {}
            self.in_contract_index[level] = {}
            self.out_contract_index[level] = {}
            self.index[level] = {}
            self.in_index[level] = {}
            self.out_index[level] = {}

            for component in self.library.components:
                contract = component.contract
                self.contracts.add(contract)
                self.contract_index[level][contract] = []
                self.in_contract_index[level][contract] = []
                self.out_contract_index[level][contract] = []

                for port in contract.input_ports_dict.values():
                    model = z3.Int('%d-%s' % (level, port.unique_name))
                    self.models.append(model)
                    self.in_models.append(model)
                    self.ports.append(port)
                    self.in_ports.append(port)
                    self.model_levels[model.get_id()] = level
                    self.model_contracts[model.get_id()] = contract

                    #reverse lookup
                    self.model_index[model.get_id()] = len(self.models) - 1
                    self.model_in_index[model.get_id()] = len(self.models) - 1
                    self.index[level][port] = len(self.models) - 1
                    self.in_index[level][port] = len(self.in_models) - 1

                    self.contract_index[level][contract].append(len(self.models) - 1)
                    self.in_contract_index[level][contract].append(len(self.in_models) - 1)

                for port in contract.output_ports_dict.values():
                    model = z3.Int('%d-%s' % (level, port.unique_name))
                    self.models.append(model)
                    self.out_models.append(model)
                    self.ports.append(port)
                    self.out_ports.append(port)
                    self.model_levels[model.get_id()] = level
                    self.model_contracts[model.get_id()] = contract

                    #reverse lookup
                    self.model_index[model.get_id()] = len(self.models) - 1
                    self.model_out_index[model.get_id()] = len(self.models) - 1
                    self.index[level][port] = len(self.models) - 1
                    self.out_index[level][port] = len(self.out_models) - 1

                    self.contract_index[level][contract].append(len(self.models) - 1)
                    self.out_contract_index[level][contract].append(len(self.out_models) - 1)



        LOG.debug({i:self.models[i] for i in range(0,self.max_index)})


    @property
    def max_index(self):
        '''
        get the highest index
        '''
        return len(self.models)

    @property
    def max_in_index(self):
        '''
        returns the highest input index
        '''
        return len(self.in_models)

    @property
    def max_out_index(self):
        '''
        returns the highest input index
        '''
        return len(self.out_models)

    @property
    def max_single_level_index(self):
        '''
        returns the max index not considering levels
        '''
        return len(self.models)/(self.max_components)

    @property
    def max_single_level_in_index(self):
        '''
        returns the max index not considering levels
        '''

        return len(self.in_models)/(self.max_components + 1)

    @property
    def max_single_level_out_index(self):
        '''
        returns the max index not considering levels
        '''

        return len(self.out_models)/(self.max_components + 1)

    def port_by_index(self, index):
        '''
        returns the port associated to the index
        '''
        return self.ports[index]

    def in_port_by_index(self, index):
        '''
        returns the port associated to the index
        '''
        return self.in_ports[index]

    def out_port_by_index(self, index):
        '''
        returns the port associated to the index
        '''
        return self.out_ports[index]

    def model_by_index(self, index):
        '''
        returns the model associated to the index
        '''
        return self.models[index]

    def in_model_by_index(self, index):
        '''
        returns the model associated to the index
        '''
        return self.in_models[index]

    def out_model_by_index(self, index):
        '''
        returns the model associated to the index
        '''
        return self.out_models[index]

    def contract_indices(self, contract):
        '''
        return all the indices for a contract
        '''
        return [self.contract_index[level][contract]
                for level in range(0, self.max_components)]

    def contract_in_indices(self, contract):
        '''
        return all the input indices for a contract
        '''
        return [self.in_contract_index[level][contract]
                for level in range(0, self.max_components)]

    def contract_out_indices(self, contract):
        '''
        return all the output indices for a contract
        '''
        return [self.out_contract_index[level][contract]
                for level in range(0, self.max_components)]

    def model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return [self.models[self.index[port]]
                for level in range(0, self.max_components)]

    def in_model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return [self.in_models[self.in_index[level][port]]
                for level in range(0, self.max_components)]

    def out_model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return [self.out_models[self.out_index[level][port]]
                for level in range(0, self.max_components)]

    def contract_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [[self.models[index]
                 for index in self.contract_index[level][contract]]
                for level in range(0, self.max_components)]

    def contract_in_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [[self.in_models[index]
                 for index in self.in_contract_index[level][contract]]
                for level in range(0, self.max_components)]

    def contract_out_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [[self.out_models[index]
                 for index in self.out_contract_index[level][contract]]
                for level in range(0, self.max_components)]

    def all_other_models(self, model):
        '''
        returns all the models minus the one given as param
        '''

        return [self.models[index] for index in range(0, self.max_index)
                if index != self.model_index[model.get_id()]]

    def all_other_in_models(self, model):
        '''
        returns all the models minus the one given as param
        '''

        return [other for other in self.in_models
                if model.get_id() != other.get_id()]

    def related_models(self, model):
        '''
        Given a model, finds all the models related to the same contract
        '''
        #infer level
        level = self.model_levels[model.get_id()]
        #get contract
        contract = self.model_contracts[model.get_id()]

        return [self.models[index]
                 for index in self.contract_index[level][contract]]

    def related_in_models(self, model):
        '''
        Given a model, finds all the models related to the same contract
        '''
        #infer level
        level = self.model_levels[model.get_id()]
        #get contract
        contract = self.model_contracts[model.get_id()]

        return [self.in_models[index]
                 for index in self.in_contract_index[level][contract]]

    def models_by_contracts(self):
        '''
        returns all the models grouped by contracts
        '''
        return [models
                for contract in self.contracts
                for models in self.contract_models(contract)]

    def models_out_by_contracts(self):
        '''
        returns all the models grouped by contracts
        '''
        return [models
                for contract in self.contracts
                for models in self.contract_out_models(contract)]

    def models_in_by_contracts(self):
        '''
        returns all the models grouped by contracts
        '''
        return [models
                for contract in self.contracts
                for models in self.contract_in_models(contract)]

    def index_by_model(self, model):
        '''
        returns the index of the model
        '''
        return self.model_index[model.get_id()]


    def contract_by_model(self, model):
        '''
        returns contract and level associate to a model
        '''
        #infer level
        level = self.model_levels[model.get_id()]
        #get contract
        contract = self.model_contracts[model.get_id()]

        return (level, contract)


    def contract_copies_by_models(self, model_list):
        '''
        makes copies of contracts considering models
        and levels, and put them in a dictionary
        '''
        levels = [{} for level in range(0, self.max_components)]
        model_map_contract = {}
        contract_map = {}

        for model in model_list:
            level, contract = self.contract_by_model(model)
            if contract not in levels[level]:
                levels[level][contract] = contract.copy()

            model_map_contract[model.get_id()] = levels[level][contract]
            contract_map[contract] = levels[level][contract]


        return model_map_contract, contract_map

    def index_shift(self, index, shift_lev):
        '''
        returns the index shifted by shift_lev position.
        works as a circular buffer
        '''
        if index == -1:
            return -1

        return (index + self.max_single_level_index * shift_lev) % self.max_index

    def index_in_shift(self, index, shift_lev):
        '''
        returns the index shifted by shift_lev position.
        works as a circular buffer
        '''
        if index == -1:
            return -1

        return (index + self.max_single_level_in_index * shift_lev) % self.max_in_index


    def build_equivalence_sets(self, specs, indices, model):
        '''
        return a list with all the possible combinations of contracts and levels
        for a given set of indices
        '''
        #get all the contracts. at most len(indices) contracts.
        #maybe less if two ports refer to the same contract and level
        contract_lev = []
        contract_map = {}
        initial_allocation = {}
        port_ref = {}
        positions = {}

        for index in indices:
            p_model = self.models[index]
            level = self.model_levels[p_model.get_id()]
            contract = self.model_contracts[p_model.get_id()]

            if (level, contract) not in contract_lev:
                #define contract position
                contract_lev.append((level, contract))

            positions.update({port: len(contract_lev)-1
                          for port in self.contract_indices(contract)[level]})

            initial_allocation[(level, contract)] = [simplify(model[self.in_models[p_index]]).as_long()
                               for p_index in self.contract_in_indices(contract)[level]]

            if (level, contract) not in port_ref:
                port_ref[(level, contract)] = []

            port_ref[(level, contract)].append(index)


        print initial_allocation
        print positions
        #build map
        #contract_map = {(level, contract): self.contract_indices(contract)[level]
        #                for contract in self.contracts
        #                for level in range(0, self.max_components)}

        #now we know how many elements we need
        num_elem = len(contract_lev)

        #shift_matrix
        #shift = [elem for elem in itertools.product(range(0, num_elem), repeat=num_elem)]
        new_indices = {}

        for elem in itertools.product(range(0, num_elem), repeat=num_elem):
            new_indices = [specs[i] == self.index_shift(indices[i], elem[positions[indices[i]]])
                           for i in range(0, len(indices))]
            print new_indices

            new_contracts = [((contract_lev[i][0] + elem[i])%self.max_components, contract_lev[i][1]) for i in range(0, num_elem)]

            print new_contracts

            #elaborate connections
            new_models = []
            for i in range(0, len(new_contracts)):
                n_l = new_contracts[i][0]
                n_c = new_contracts[i][1]

                o_l = contract_lev[i][0]
                o_c = contract_lev[i][1]

                p_inds = self.contract_in_indices(o_c)[o_l]
                values = initial_allocation[(o_l, o_c)]

                for index, value in zip(p_inds, values):
                    new_p_ind = self.index_in_shift(index, elem[i])
                    new_p = self.in_models[new_p_ind]

                    if value == -1:
                        new_value = -1
                    else:
                        new_value = self.index_shift(value, elem[positions[value]])

                    new_models.append(new_p == new_value)

            print new_models
            yield new_indices + new_models


            #new_models = [[self.models[self.index_shift(port, elem[positions[port]])] == self.index_shift(initial_allocation[simplify(model[self.models[port]]).as_long()], elem[positions[simplify(model[self.models[port]]).as_long()]])
            #               for port in self.contract_in_indices(contract_lev[i][1])[contract_lev[i][0]]]
             #             for i in range(0, len(new_contracts))]

            print new_models
        #print shift

        print 'done'


class Z3Interface(object):
    '''
    Interface class for the Z3 SMT solver.
    Extends the class SMTModelFactory
    '''

    def __init__(self, library):
        '''
        init
        '''

        set_param(proof=True)
        self.library = library
        #selfeset = library.typeset
        self.type_compatibility_set = library.type_compatibility_set
        self.max_hierarchy = library.max_hierarchy
        self.refined_by = library.refined_by
        self.refines = library.refines
        self.hierarchy = library.hierarchy

        #constraints by components
        self.distinct_ports_by_component = {}

        self.property_model = None
        self.property_contract = None
        self.specification_list = []
        self.num_out = 0
        #self.ComponentBaseName = None

        self.contracts_dict = {}
        #self.portc_types = {}
        #self.mapping_datatypes = {}
        #self.mapping_pairs = {}
        self.contract_model_instances = {}
        self.port_names = set()

        #TODO remember to include mapping
        self.component_refinement = None

        #hints from designer
        self.same_block_constraints = None
        self.distinct_mapping_constraints = None

        self.counter = itertools.count()
        self.port_dict = {}

        #maintain a list of contracts to check for consistency
        self.consistency_dict = {}

        self.solver = None

    @property
    def extended_instances(self):
        '''
        returns library instances plus property model
        '''
        assert self.property_model is not None

        return dict(self.contract_model_instances.items() + [(self.property_model, self.property_contract)])


    def initiliaze_solver(self, property_contract):
        '''
        Create environment and models from library
        '''

        port_name_pairs = self.library.smt_manager.port_name_pairs
        contract_name_pairs = self.library.smt_manager.contract_name_pairs
        component_name_pairs = self.library.smt_manager.component_name_pairs


        #extend port names with property ones
        _ = [port_name_pairs.append((port.base_name, port.unique_name))
             for port in property_contract.ports_dict.values()]

        #extends contract names
        contract_name_pairs.append((property_contract.base_name, property_contract.unique_name))


        #self.property_model = self.create_contract_model(property_contract, 0, is_library_elem=False)
        self.property_contract = property_contract

        self.create_z3_environment(self.property_contract)


    def create_z3_environment(self, spec):
        '''
        Creates basic types for the current library instance
        '''

        self.spec_outs = [z3.Int('%s' % name) for name in spec.output_ports_dict]
        self.spec_ins = [z3.Int('%s' % name) for name in spec.input_ports_dict]
        self.num_out = len(self.spec_outs)

        self.lib_model = Z3Library(self.library, spec)

        #LOG.debug(self.lib_model.models_by_contracts())

        self.solver = Solver()

        LOG.debug('ok')
        LOG.debug(self.lib_model)



    def exclude_candidate_type(self, candidate, discarded_model):
        '''
        make sure that a future solution will not include any contract
        identycal to the one discarded
        '''
        constraints = []

        model_contract = self.extended_instances[discarded_model]
        #constraints.append(candidate != discarded_model)

        #for (model, contract) in self.extended_instances.items():
        #    if contract.base_name == model_contract.base_name:
        #        constraints.append(candidate != discarded_model)

        constraints = [candidate != discarded_model
                       for (model, contract) in self.extended_instances.items()
                       if contract.base_name == model_contract.base_name]

        return constraints




    def all_zero(self):
        '''
        all zeros
        '''
        constraints = []
        constraints = [port == 0 for port in self.spec_ins]
        constraints += [port == 0 for port in self.spec_outs]
        constraints += [model == 0 for model in self.lib_model.models]

        self.solver.add(constraints)

    def lib_distinct(self):
        '''
        all the outputs must be zeros or connected to a spec out,
        but distinct.
        At least a model is connected to output

        '''

        constraints = []
        constraints += [model >= -1 for model in self.lib_model.in_models]
        constraints += [model <= self.num_out for model in self.lib_model.in_models]
        constraints += [Or(model == -1,
                           And([model != other
                                for other in self.lib_model.all_other_in_models(model)]))
                        for model in self.lib_model.in_models]

        #constraints += [Or([model == index for model in self.lib_model.models])
        #                for index in range(1, self.num_out + 1)]

        self.solver.add(constraints)

    def full_spec_out(self):
        '''
        all the outputs must be connected (0 < spec < max),
        but distinct.

        '''

        constraints = []
        constraints += [port > -1 for port in self.spec_outs]
        constraints += [port < self.lib_model.max_index for port in self.spec_outs]
        constraints += [Distinct(self.spec_outs)]

        self.solver.add(constraints)

    def spec_out_to_out(self):
        '''
        a spec out can connect only to another output
        '''

        constraints = []
        print self.lib_model.max_single_level_index
        #get all the duplicates
        constraints += [And([model != (index + self.lib_model.max_single_level_index*level)
                             for level in range(0, self.lib_model.max_components)
                             for index in range(0, self.lib_model.max_single_level_index)
                             if self.lib_model.port_by_index(index).is_input])
                        for model in self.spec_outs]

        #LOG.debug(constraints)

        self.solver.add(constraints)

    def full_spec_in(self):
        '''
        all the inputs must be connected (0 < spec < max),
        but distinct.

        '''

        constraints = []
        constraints += [port > -1 for port in self.spec_ins]
        constraints += [port < self.lib_model.max_index for port in self.spec_ins]
        constraints += [Distinct(self.spec_ins)]

        self.solver.add(constraints)

    def spec_in_to_in(self):
        '''
        a spec input can connect only to another input
        '''

        constraints = []
        constraints += [And([model != (index + self.lib_model.max_single_level_index*level)
                             for level in range(0, self.lib_model.max_components)
                             for index in range(0, self.lib_model.max_index)
                             if self.lib_model.port_by_index(index).is_output])
                        for model in self.spec_ins]

        #LOG.debug(constraints)

        self.solver.add(constraints)

    def inputs_from_selected(self):
        '''
        inputs only to non-zero ports
        '''

        constraints = []
        #constraints += [And([Implies(port == self.lib_model.index_by_model(model),
        #                             model > -1)
        #                     for model in self.lib_model.in_models]
        #                   )
        #                for port in self.spec_ins]


        constraints += [Implies(And([And([spec_out != self.lib_model.index_by_model(model)
                                          for model
                                          in self.lib_model.contract_out_models(contract)[level]])
                                     for spec_out in self.spec_outs]),
                                And([And([port != self.lib_model.index_by_model(model)
                                         for model in self.lib_model.contract_in_models(contract)[level]])
                                     for port in self.spec_ins])
                                )
                        for contract in self.lib_model.contracts
                        for level in range(0, self.num_out)]

      

        self.solver.add(constraints)

    def lib_chosen_not_zeros(self):
        '''
        If a component is not chosen, then it's all zeros.

        '''

        constraints = []
        constraints += [And([Implies(spec_port == index,
                                     And([And(model >= -1,
                                              model < self.lib_model.max_index)
                                          for model
                                            in self.lib_model.related_in_models(self.lib_model.model_by_index(index))]))
                             for index in range(0, self.lib_model.max_index)])
                        for spec_port in self.spec_outs]


        self.solver.add(constraints)

    def spec_inputs_no_feedback(self):
        '''
        spec inputs cannot be connected
        '''

        constraints = []
        constraints += [And([Implies(port == self.lib_model.index_by_model(model),
                                     model == -1)
                             for model in self.lib_model.in_models]
                           )
                        for port in self.spec_ins]

        self.solver.add(constraints)


    def lib_to_outputs(self):
        '''
        If a component is not chosen, then it's all zeros.

        '''

        constraints = []

        constraints += [And([model != (index + self.lib_model.max_single_level_index*level)
                             for level in range(0, self.lib_model.max_components)
                             for index in range(0, self.lib_model.max_single_level_index)
                             if self.lib_model.port_by_index(index).is_input])
                        for model in self.lib_model.in_models]

        print constraints

        self.solver.add(constraints)

    def lib_chosen_to_chosen(self):
        '''
        Input of a chosen contract can be connected only to the output of a chosen contract
        '''
        constraints = []

        constraints += [Implies(And([And([spec_out != self.lib_model.index_by_model(model)
                                          for model
                                          in self.lib_model.contract_out_models(contract)[level]])
                                     for spec_out in self.spec_outs]),
                                And([And([port != self.lib_model.index_by_model(model)
                                         for model in self.lib_model.contract_out_models(contract)[level]])
                                     for port in self.lib_model.in_models])
                                )
                        for contract in self.lib_model.contracts
                        for level in range(0, self.num_out)]



        print constraints

        self.solver.add(constraints)

    def lib_not_chosen_zero(self):
        '''
        if no ports are selected from a contract, all the output are zero
        '''

        constraints = []
        constraints += [Implies(And([And([spec_out != self.lib_model.index_by_model(model)
                                          for model
                                          in self.lib_model.contract_out_models(contract)[level]])
                                     for spec_out in self.spec_outs]),
                                And([model == -1 for model in self.lib_model.contract_in_models(contract)[level]])
                                )
                        for contract in self.lib_model.contracts
                        for level in range(0, self.num_out)]


        self.solver.add(constraints)

    def synthesize(self, property_contracts, same_block_constraints,
                    distinct_mapping_constraints):
        '''
        perform synthesis process
        '''
        self.time = {}
        self.time['start'] = time()
        self.same_block_constraints = same_block_constraints
        self.distinct_mapping_constraints = distinct_mapping_constraints

        self.specification_list = property_contracts

        #let's pick a root
        #we assume all the specs have same interface
        property_contract = self.specification_list[0]

        self.initiliaze_solver(property_contract)

        max_components = len(property_contract.output_ports_dict)

        #property model has to be fully connected - always true
        #self.solver.add(self.fully_connected(self.property_model))

        #self.all_zero()
        LOG.debug(property_contract)
        self.full_spec_out()
        self.spec_out_to_out()
        self.full_spec_in()
        self.spec_in_to_in()
        self.spec_inputs_no_feedback()
        self.inputs_from_selected()
        self.lib_chosen_not_zeros()
        self.lib_to_outputs()
        self.lib_chosen_to_chosen()
        self.lib_not_chosen_zero()
        #self.lib_distinct()


        LOG.debug(self.lib_model.models_by_contracts())
        LOG.debug(self.lib_model.models_in_by_contracts())
        #LOG.debug(self.solver.assertions())



        while True:
            try:
                model = self.propose_candidate()
            except NotSynthesizableError as err:
                raise err
            else:
                try:
                    composition, spec, contract_list = self.verify_candidate(model)
                except NotSynthesizableError as err:
                    LOG.debug("candidate not valid")
                else:
                    return 0
                    return model, composition, spec, contract_list


    def propose_candidate(self):
        '''
        generate a model
        '''

        LOG.debug('start solving')
        res = self.solver.check()
        LOG.debug(res)
        if res == sat:
            #LOG.debug(self.solver.model())
            #LOG.debug('func eval')
            #LOG.debug(self.solver.model()[self.fully_connected])
            pass
        else:
            #LOG.debug(self.solver.proof())
            pass

        try:
            model = self.solver.model()
        except Z3Exception:
            raise NotSynthesizableError()
        else:
            for spec in self.spec_ins:
                LOG.debug('%s -> %s'
                    % (spec, self.lib_model.model_by_index(simplify(model[spec]).as_long())))
            for spec in self.spec_outs:
                LOG.debug('%s -> %s'
                    % (spec, self.lib_model.model_by_index(simplify(model[spec]).as_long())))

            LOG.debug(model)


        return model

    def verify_candidate(self, model):
        '''
        check if a candidate is valid or not.
        Here we need to:
        1) transform the model to a contract composition
        2) LEARN
            2a)
        '''

        #self.reject_candidate(model, candidates)
        state, composition, connected_spec, contract_inst = \
                self.check_all_specs(model)
        if not state:
            #learn
            #as first step, we reject the actual solution
            #self.solver.add(self.exclude_candidate_type())
            #LOG.debug('exclude')
            #LOG.debug(z3.Not(self.connected_ports==model[self.connected_ports]))
            #self.solver.add(z3.Not(self.connected_ports==model[self.connected_ports]))
            self.reject_candidate(model)

            #then check for consistency
            #self.solver.add(self.check_for_consistency(model, contract_inst, connected_spec))

            raise NotSynthesizableError

        return composition, connected_spec, contract_inst

    def check_all_specs(self, model):
        '''
        check if the model satisfies a number of specs, if provided
        '''
        composition = None
        connected_spec = None
        contract_inst = None
        for spec in self.specification_list:
            composition, connected_spec, contract_inst = \
                    self.build_composition_from_model(model, spec, complete_model=True)

            LOG.debug('ref check')
            if not composition.is_refinement(connected_spec):
                LOG.debug('ref check done 1')
                return False, composition, connected_spec,contract_inst

            LOG.debug('ref check done 2')

        return True, composition, connected_spec,contract_inst


    def build_composition_from_model(self, model, spec, complete_model=True):
        '''
        builds a contract composition out of a model
        '''

        #contracts = set()
        spec_contract = spec.copy()

        #LOG.debug(spec_contract)

        #find all contracts from model
        #a set will help us remove duplicates
        #contracts = set()

        #get all the models, checking outputs
        models = [self.lib_model.model_by_index(simplify(model[port]).as_long()) for port in self.spec_outs]

        #now we get all the contracts related.
        #by construction fetching only the outputs, we have the full set of contracts
        model_map, contract_map = self.lib_model.contract_copies_by_models(models)

        LOG.debug(model_map)
        LOG.debug(contract_map)

        contracts = set(model_map.values())
        #extended_contracts = dict(list(contracts) + [spec_contract])

        #start composition
        #c_set = contracts
        #c_set.add(contracts.values()[0])
        mapping = CompositionMapping(contracts)

        #start witn spec
        for p_model in self.spec_outs + self.spec_ins:
            name = str(p_model)

            spec_port = spec_contract.ports_dict[name]

            index = simplify(model[p_model]).as_long()
            orig_port = self.lib_model.port_by_index(index)

            other_contract_orig = orig_port.contract
            other_contract = contract_map[other_contract_orig]

            port = other_contract.ports_dict[orig_port.base_name]

            spec_contract.connect_to_port(spec_port, port)


        #connections among candidates
        #non_zero_port_models = [p_model for p_model in self.lib_model.in_models
        #                        if simplify(model[p_model]).as_long() > -1]
        for old_contract in contract_map:
            current_contract = contract_map[old_contract]

            for old_in_port in old_contract.input_ports_dict:
                current_port = current_contract.ports_dict[old_in_port]

                if simplify(model[p_model]).as_long() > -1:
                    other_index = simplify(model[p_model]).as_long()

                    other_port_orig = self.lib_model.port_by_index(other_index)

                    other_contract = contract_map[other_port_orig.contract]

                    other_port = other_contract.ports_dict[other_port_orig.base_name]

                    mapping.connect(current_port, other_port,
                                    '%s_%s' % (current_contract.unique_name,
                                               current_port.base_name))
                else:
                    mapping.add(current_port, '%s_%s' % (current_contract.unique_name,
                                                         current_port.base_name))

            for old_out_port in old_contract.output_ports_dict:
                current_port = current_contract.ports_dict[old_out_port]

                mapping.add(current_port, '%s_%s' % (current_contract.unique_name,
                                                     current_port.base_name))


        for contract in contracts:
            LOG.debug(contract)
        LOG.debug(spec_contract)

        if not complete_model:
            c_set = self.filter_candidate_contracts_for_composition(contracts, spec_contract)

        #compose
        root = contracts.pop()

        #c_set.add(root.copy())

        composition = root.compose(contracts, composition_mapping=mapping)

        LOG.debug(composition)
        LOG.debug(spec_contract)

        return composition, spec_contract, contracts




    def reject_candidate(self, model):
        '''
        reject model
        '''
        #import pdb
        #pdb.set_trace()

        #identify involved contracts in formula
        #TODO

        #all for now. include copies...
        constraints = []

        #we need to reject the current model, plus all the possible combinations
        #of redundant copies...

        selected_indices = [simplify(model[p_model]).as_long() for p_model in self.spec_ins + self.spec_outs]

        for excluded in self.lib_model.build_equivalence_sets(self.spec_ins + self.spec_outs, selected_indices, model):

            LOG.debug(Not(And(excluded)))
            self.solver.add(Not(And(excluded)))

        LOG.debug('add rejected models constraints')


    def connected_output(self, candidate):
        '''
        spec and candidate have to have a output pirt in common
        '''
        constraints = [Implies(candidate == m_a,
                                  Or([self.connected_ports(self.property_model,
                                                            candidate,
                                                self.port_dict[n_p],
                                                self.port_dict[n_a])
                                  for n_p in self.property_contract.output_ports_dict
                                  for n_a in c_a.output_ports_dict]
                                        )
                                  )
                        for m_a, c_a in self.contract_model_instances.items()]

        return constraints

    def synthesize_fixed_size(self, size):
        '''
        synthesis for a fixed size
        includes constraints:
        we expect 'size' components and (size-1)! mappings.
        1) We need to generate a candidate
        2) We need to verify refinement

        1) We need to create this variables and assert the possibilities
        2) We also need to create the mapping functions. Do we allow feedback? Not for now.
        3) We need to define the refinement relations, where possible. Low priority
        4) Verify and loop


        '''
        self.time['size%s' % size] = time()
        self.initialize_for_fixed_size(size)

        #declare variables
        c_list = [Const('c_%s' % i, self.ZContract) for i in range(0, size)]

        #constraints = []

        print '4'
        #Every component must be unique (we already duplicated)
        self.solver.add([Distinct(c_list)])

        print '5'
        #All the candidates fully connected
        self.solver.add(self.all_models_completely_connected(c_list))

        print '6'
        #property has to be fully connected
        self.solver.add([self.fully_connected(self.property_model)])

        #Spec cannot be connected to itself on outputs
        #self.solver.add(self.connected_output(self.property_model, self.property_model)==False)
        #self.solver.add(self.property_outputs_not_together())

        print '7'
        #property inputs only with inputs
        #prevents evil feedback
        self.solver.add(self.property_inputs_no_on_candidate_outputs())

        print '8'
        #models disconnected if not solution
        self.solver.add(self.models_disconnected_if_not_solution(c_list))

        print '9'
        #property inputs have to be conncted to model inputs
        self.solver.add(self.property_inputs_to_candidates())

        print '10'
        #property outputs have to be connected to model outputs
        self.solver.add(self.property_outputs_to_candidates())

        #add full input for models, too
        #---nope

        print '11'
        #add input needs to be connected to property
        #or outputs
        self.solver.add(self.inputs_on_property_inputs_or_candidate_out(c_list))

        print '12'
        #from previous computation
        self.solver.add(self.recall_not_consistent_constraints())

        print '13'
        #external hints
        self.solver.add(self.compute_same_block_constraints())
        print '14'
        self.solver.add(self.compute_distinct_port_constraints())

        print '15'
        #type compatibility
        self.solver.add(self.process_candidate_type_compatibility())
        print '16'
        self.solver.add(self.process_spec_type_compatibility())

        print '17'
        #library constraints
        self.solver.add(self.compute_component_port_constraints())

        print '18'
        for candidate in c_list:
            #candidates must be within library components
            span = [candidate == component for component in self.contract_model_instances]
            self.solver.add([Or(span)])

            #but candidate cannot be the spec itself
            self.solver.add([Not(candidate==self.property_model)])

            #spec needs to be connected to candidates
            #self.solver.add([self.connected_output(candidate, self.property_model)])
            #self.solver.add(self.connected_output(candidate))

        #self.solver.add(constraints)

        self.time['size%s' % size] = time() - self.time['size%s' % size]

        current_hierarchy = 0
        LOG.debug('current hierarchy: %d' % current_hierarchy)


        while True:
            try:
                #push current hierarchy level
                #pop is done in the finally clause
                self.solver.push()
                self.solver.add(self.allow_hierarchy(current_hierarchy, c_list))
                model = self.propose_candidate(size)
                self.solver.pop()
            except NotSynthesizableError as err:
                if current_hierarchy < self.max_hierarchy:
                    LOG.debug('increase hierarchy to %d' % (current_hierarchy + 1))
                    current_hierarchy += 1
                    self.solver.pop()
                    #self.solver.push()
                    #self.solver.add(self.allow_hierarchy(current_hierarchy, c_list))
                    #LOG.debug(self.solver.assertions)
                else:
                    self.solver.pop()
                    raise err
            else:
                try:
                    composition, spec, contract_list = self.verify_candidate(model, c_list)
                except NotSynthesizableError as err:
                    LOG.debug("candidate not valid")
                else:

                    #(composition,
                    # spec_contract,
                    # contracts) = self.build_composition_from_model(model,
                    #                                                self.property_contract,
                    #                                                c_list,
                    #                                                complete_model=True)
                    return model, composition, spec, contract_list
                

    def allow_hierarchy(self, hierarchy, candidate_list):
        '''
        Allows components with hierarchy less than or equal to hierarchy
        '''
        constraints = [self.ZContract.hierarchy(candidate) <= BitVecVal(hierarchy,2)
                         for candidate in candidate_list]

        return constraints









    def check_for_consistency(self, model, candidates, contract_instances, spec_contract):
        '''
        Checks for consistency of contracts in the proposed model.
        If inconsistent, remove the contract and its refinements from
        the possible candidates.
        Steps.
            1) take a model from the candidate list
            2) make a copy of the spec contract
            3) for every common output port between model and spec:
                3.1) connect the only port of model with spec
                3.2) compose model with spec
                3.3) check consistency
                3.4) if inconsistent, remove model and port from solution space
        '''

        constraints = []


        #instantiate single contracts
        for candidate in candidates:
            c_m = model[candidate]
            c_m.__hash__ = types.MethodType(zcontract_hash, c_m)
            c_name = str(simplify(self.ZContract.base_name(c_m)))

            #get base instance
            contract = contract_instances[c_m]

            if c_name not in self.consistency_dict:
                self.consistency_dict[c_name] = {}

            #contracts[c_m] = contract

            for (port_name_a, port_name_spec) in (
                itertools.product(contract.output_ports_dict,
                    spec_contract.output_ports_dict)):

                p_a = getattr(self.PortBaseName, port_name_a)
                p_s = getattr(self.PortBaseName, port_name_spec)

                condition = is_true(model.eval(self.connected_ports(c_m,
                                                                       self.property_model,
                                                                       p_a, p_s),
                                                  model_completion=True))

                if ((port_name_a, port_name_spec) not in self.consistency_dict[c_name]
                     and condition):

                    LOG.debug('Checking consistency of %s: %s->%s' % (contract.base_name,
                                                                  port_name_a,
                                                                  port_name_spec))

                    #LOG.debug(self.consistency_dict)
                    self.consistency_dict[c_name][(port_name_a, port_name_spec)] = True

                    #reinstantiate a fresh copy of contract
                    LOG.debug('pre copy')
                    spec_contract = spec_contract.copy()
                    LOG.debug('post copy')
                    #spec model is the same for all specs

                    contract = type(self.contract_model_instances[c_m])(c_name)


                    port_a = contract.output_ports_dict[port_name_a]
                    port_spec = spec_contract.output_ports_dict[port_name_spec]

                    spec_contract.connect_to_port(port_spec, port_a)

                    c_mapping = CompositionMapping([spec_contract, contract])
                    #names
                    for port in spec_contract.ports_dict.values():
                        c_mapping.add(port_a, '%s_%s' % (contract.unique_name,
                                                         port_a.base_name))
                    for port in contract.ports_dict.values():
                        c_mapping.add(port_spec, '%s_%s' % (spec_contract.unique_name,
                                                        port_spec.base_name))

                    composition = spec_contract.compose(contract,
                                                        composition_mapping=c_mapping)
                    if not composition.is_consistent():
                        LOG.debug('NOT CONSISTENT')

                        self.consistency_dict[c_name][(port_name_a, port_name_spec)] = False
                        constraints += [Not(self.connected_ports(c_a, self.property_model,
                                                                p_a, p_s))
                                        for c_a in self.contract_model_instances
                                        if str(simplify(self.ZContract.base_name(c_a)))
                                           == c_name
                                        ]
                        #add constraints also for the contracts which refines this one
                        for ref_name in self.refines[c_name]:
                            ref_map = self.refines[c_name][ref_name]
                            mapped_p_name = ref_map[port_name_a]
                            mapped_p = getattr(self.PortBaseName, mapped_p_name)
                            self.consistency_dict[ref_name][(mapped_p_name,
                                                             port_name_spec)] = False

                            constraints += [Not(self.connected_ports(c_a, self.property_model,
                                                                mapped_p, p_s))
                                        for c_a in self.contract_model_instances
                                        if str(simplify(self.ZContract.base_name(c_a)))
                                           == ref_name
                                        ]
        #LOG.debug('consistency constraints')
        #LOG.debug(constraints)
        return constraints

    def recall_not_consistent_constraints(self):
        '''
        to be called by sizes > 1.
        Load all the informations related to inconsistent
        blocks, computed in previous steps
        '''
        constraints = [Not(self.connected_ports(c_a, self.property_model,
                                                   getattr(self.PortBaseName, port_name_a),
                                                   getattr(self.PortBaseName, port_name_s)))
                       for c_name, name_set in self.consistency_dict.items()
                       for c_a in self.contract_model_instances
                       if str(simplify(self.ZContract.base_name(c_a)))
                                           == c_name
                       for (port_name_a, port_name_s) in name_set
                       if self.consistency_dict[c_name][(port_name_a, port_name_s)]==False
                       ]
        #LOG.debug(constraints)
        return constraints


    def filter_candidate_contracts_for_composition(self, candidates, spec_contract):
        '''
        Figures out what candidates are really needed to perform refinement verification
        '''
        #TODO: can you prove this please?
        #consider to add also all the input of the spec...and close the loop
        #the other way
        #if len(candidates) > 1:
        #    import pdb
        #    pdb.set_trace()
        spec_literals = spec_contract.assume_formula.get_literal_items()
        spec_literals |= spec_contract.guarantee_formula.get_literal_items()
        spec_literal_unames = set([literal.unique_name for (_,literal) in spec_literals])

        #match ports on literals
        out_ports = {name: port for name, port in spec_contract.output_ports_dict.items()
                     if port.unique_name in spec_literal_unames}

        in_ports = {name: port for name, port in spec_contract.input_ports_dict.items()
                     if port.unique_name in spec_literal_unames}

        #push all the output ports into a stack, and start exploring
        explore_list = set(out_ports.values())
        connected_contracts = set()

        #find all candidates connected to the spec
        while explore_list:
            new_ports = set()
            query_port = explore_list.pop()
            for contract in candidates:
                if contract not in connected_contracts:
                    for port in contract.output_ports_dict.values():
                        if port.is_connected_to(query_port):
                            connected_contracts.add(contract)
                            new_ports |= set(([n_port for n_port
                                           in contract.input_ports_dict.values()]))
                            break

            explore_list |= new_ports

        LOG.debug('filtered list')
        LOG.debug(connected_contracts)
        return connected_contracts






SMTModelFactory.register(Z3Interface)


class NotSynthesizableError(Exception):
    '''
    raised if it is not possible to synthesize a controller
    '''
    pass

#instance a public interface
#Z3 = Z3Interface()

