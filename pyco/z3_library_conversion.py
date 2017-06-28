'''
This module builds the structure converting the contract library to datatypes
for the Z3 SMT solver

Author: Antonio Iannopollo
'''

#import logging
from pyco.formula import (Conjunction, Disjunction, Negation,
                          Implication, Equivalence, TrueFormula, FalseFormula)
from z3 import *

from pyco import LOG

#LOG = logging.getLogger()
LOG.debug('in z3_library_conversion')

MAX_REDUNDANCY = 2

def convert_formula_to_z3(formula, contract_vars, level):
    '''
    return a Z3 formula from a pyco-lite-lite-dev formula structure
    '''

    if formula.is_literal:
        return contract_vars['%d-%s' % (level, formula.unique_name)]
    elif isinstance(formula, TrueFormula):
        return True
    elif isinstance(formula, FalseFormula):
        return False
    elif isinstance(formula, Negation):
        return Not(convert_formula_to_z3(formula.right_formula,
            contract_vars, level))
    elif isinstance(formula, Conjunction):
        return And(convert_formula_to_z3(formula.left_formula,
                                                contract_vars, level),
         convert_formula_to_z3(formula.right_formula, contract_vars, level))
    elif isinstance(formula, Disjunction):
        return Or(convert_formula_to_z3(formula.left_formula,
                                                    contract_vars, level),
         convert_formula_to_z3(formula.right_formula, contract_vars, level))
    elif isinstance(formula, Implication):
        return Implies(convert_formula_to_z3(formula.left_formula,
                                                        contract_vars, level),
         convert_formula_to_z3(formula.right_formula, contract_vars, level))
    elif isinstance(formula, Equivalence):
        return (convert_formula_to_z3(formula.left_formula,
                                                        contract_vars, level)
         == convert_formula_to_z3(formula.right_formula, contract_vars, level))
    else:
        LOG.critical('incorrect unrolled formula')

class Z3Library(object):
    '''
    maps library to a set of integers
    '''


    # def _contract_unrolled_formula(self, contract, level):
    #     '''
    #     associate a boolean formula to every component
    #     '''
    #     contract_vars = {'%d-%s' % (level, port.unique_name) :
    #                 Bool('%d-%s' % (level, port.unique_name))
    #                 for port in contract.ports_dict.values()}
    #
    #     #LOG.debug(contract)
    #     #LOG.debug(contract_vars)
    #
    #     unrolled_assume_formula = contract.assume_formula.unroll_1step()
    #     unrolled_guarantee_formula = contract.guarantee_formula.unroll_1step()
    #
    #     assumptions = convert_formula_to_z3(unrolled_assume_formula,
    #      contract_vars, level)
    #     guarantees = convert_formula_to_z3(unrolled_guarantee_formula,
    #      contract_vars, level)
    #
    #     #LOG.debug(unrolled_assume_formula.generate())
    #     #LOG.debug(assumptions)
    #     #LOG.debug(unrolled_guarantee_formula.generate())
    #     #LOG.debug(guarantees)
    #
    #     return (contract_vars, assumptions, guarantees)
    #
    #
    # def get_unrolled_equiv(self, specs):
    #     '''
    #     return the 1step-unrolled formula to satisfy
    #     '''
    #
    #     part_guar = []
    #     part_assm = []
    #     all_vars = {}
    #     for contract in self.unrolled_info:
    #         for level in self.unrolled_info[contract]:
    #             p1 = self.unrolled_info[contract][level]['cflag'] == 0
    #             p2 = self.unrolled_info[contract][level]['unroll_guarantee']
    #             part_guar.append(And(p1,p2))
    #
    #             p3 = self.unrolled_info[contract][level]['unroll_assume']
    #             part_assm.append(And(p1, p3))
    #
    #             all_vars.update(self.unrolled_info[contract][level]['vars'])
    #
    #     big_guar = And(part_guar)
    #     big_assm = Or(And(part_assm), Not(big_guar))
    #
    #     constraints = []
    #     #unroll specs
    #     for spec in specs:
    #         bool_vars, spec_a, spec_g = self._contract_unrolled_formula(spec, 0)
    #
    #         a_impl = Implies(spec_a, big_assm)
    #         g_impl = Implies(big_guar, spec_g)
    #
    #         constraints.append(And(a_impl, g_impl))
    #
    #         all_vars.update(bool_vars)
    #
    #     #LOG.debug(constraints[0])
    #
    #     #constraints on ports
    #     for model in self.in_models:
    #         port = self.port_by_model(model)
    #         level = self.model_levels[model.get_id()]
    #         var_name = '%d-%s' % (level, port.unique_name)
    #         for index in range(0, self.max_index):
    #             other_port = self.port_by_index(index)
    #             other_model = self.models[index]
    #             other_level = self.model_levels[other_model.get_id()]
    #             other_var_name = '%d-%s' % (other_level, other_port.unique_name)
    #             p1 = (model == index)
    #             p2 = (all_vars[var_name] == all_vars[other_var_name])
    #
    #             conn_constr = Implies(p1, p2)
    #             constraints.append(conn_constr)
    #
    #         #model to spec
    #         for index in range(self.specs_at, self.positions):
    #             other_port_name = self.spec_by_index_map[index]
    #             other_port = self.spec.input_ports_dict[other_port_name]
    #             other_var_name = '%d-%s' % (0, other_port.unique_name)
    #             p1 = (model == index)
    #             p2 = (all_vars[var_name] == all_vars[other_var_name])
    #
    #             conn_constr = Implies(p1, p2)
    #             constraints.append(conn_constr)
    #
    #     #spec_outputs
    #     for port in self.spec.output_ports_dict.values():
    #         var_name = '%d-%s' % (0, port.unique_name)
    #         for index in range(0, self.max_index):
    #             other_port = self.port_by_index(index)
    #             other_model = self.models[index]
    #             other_level = self.model_levels[other_model.get_id()]
    #             other_var_name = '%d-%s' % (other_level, other_port.unique_name)
    #             p1 = (model == index)
    #             p2 = (all_vars[var_name] == all_vars[other_var_name])
    #
    #
    #     return constraints





    def __init__(self, library, spec, limit=None):
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
        self.contract_used_by_models = {}
        self.contract_use_flags = []
        self.reverse_flag = {}
        self.flag_map = {}

        self.unrolled_info = {}

        self.spec = spec

        if limit is None:
            limit = len(spec.output_ports_dict)
        LOG.debug(limit)
        self.max_components = min([MAX_REDUNDANCY, limit])

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

                c_flag = Int('%s-%d' % (contract.base_name, level))
                self.contract_use_flags.append(c_flag)
                self.reverse_flag[c_flag.get_id()] = []
                self.flag_map['%s-%d' % (contract.base_name, level)] = c_flag

                #START UNROLL COMMENT
                #(bool_vars, unr_a, unr_g) = self._contract_unrolled_formula(contract, level)

                #if contract not in self.unrolled_info:
                #    self.unrolled_info[contract] = {}
                #if level not in self.unrolled_info[contract]:
                #    self.unrolled_info[contract][level] = {}

                #self.unrolled_info[contract][level]['cflag'] = c_flag
                #self.unrolled_info[contract][level]['vars'] = bool_vars
                #self.unrolled_info[contract][level]['unroll_assume'] = unr_a
                #self.unrolled_info[contract][level]['unroll_guarantee'] = unr_g
                #END UNROLL COMMENT


                for port in contract.input_ports_dict.values():
                    model = z3.Int('%d-%s' % (level, port.unique_name))
                    self.models.append(model)
                    self.in_models.append(model)
                    self.ports.append(port)
                    self.in_ports.append(port)
                    self.model_levels[model.get_id()] = level
                    self.model_contracts[model.get_id()] = contract

                    #contract_indexing
                    self.contract_used_by_models[len(self.models) - 1] = c_flag
                    #self.reverse_flag[c_flag.get_id()].append(len(self.models) -1)

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

                    #contract_indexing
                    self.contract_used_by_models[len(self.models) - 1] = c_flag
                    self.reverse_flag[c_flag.get_id()].append(len(self.models) -1)

                    #reverse lookup
                    self.model_index[model.get_id()] = len(self.models) - 1
                    self.model_out_index[model.get_id()] = len(self.models) - 1
                    self.index[level][port] = len(self.models) - 1
                    self.out_index[level][port] = len(self.out_models) - 1

                    self.contract_index[level][contract].append(len(self.models) - 1)
                    self.out_contract_index[level][contract].append(len(self.out_models) - 1)


        LOG.debug({i:self.models[i] for i in range(0,self.max_index)})


    def include_spec_inputs(self, spec_contract):
        '''
        assign an id also to spec_ids
        '''

        self.spec_contract = spec_contract
        self.spec_map = {}
        self.spec_by_index_map = {}
        m_index = len(self.models)

        for name, port in spec_contract.input_ports_dict.items():
            self.spec_map[name] = m_index
            self.spec_by_index_map[m_index] = name

            m_index = m_index + 1

        self.specs_at = len(self.models)
        self.positions = m_index


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

        return len(self.in_models)/(self.max_components)

    @property
    def max_single_level_out_index(self):
        '''
        returns the max index not considering levels
        '''

        return len(self.out_models)/(self.max_components)

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

    def port_by_model(self, model):
        '''
        returns the port given a model
        '''
        return self.ports[self.model_index[model.get_id()]]

    def model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return [self.models[self.index[level][port]]
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

    def related_out_models(self, model):
        '''
        Given a model, finds all the models related to the same contract
        '''
        #infer level
        level = self.model_levels[model.get_id()]
        #get contract
        contract = self.model_contracts[model.get_id()]

        return [self.out_models[index]
                 for index in self.out_contract_index[level][contract]]

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
            contract_map[(level, contract)] = levels[level][contract]


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
