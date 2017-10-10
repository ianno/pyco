'''
This module builds the structure converting the contract library to datatypes
for the Z3 SMT solver

Author: Antonio Iannopollo
'''

from pycolite.formula import (Conjunction, Disjunction, Negation,
                          Implication, Equivalence, TrueFormula, FalseFormula)
from z3 import *

from pyco import LOG

LOG.debug('in z3_library_conversion')

DEFAULT_MAX_REDUNDANCY = 1


# def convert_formula_to_z3(formula, contract_vars, level):
#     '''
#     return a Z3 formula from a pycolite-dev formula structure
#     '''
#
#     if formula.is_literal:
#         return contract_vars['%d-%s' % (level, formula.unique_name)]
#     elif isinstance(formula, TrueFormula):
#         return True
#     elif isinstance(formula, FalseFormula):
#         return False
#     elif isinstance(formula, Negation):
#         return Not(convert_formula_to_z3(formula.right_formula,
#             contract_vars, level))
#     elif isinstance(formula, Conjunction):
#         return And(convert_formula_to_z3(formula.left_formula,
#                                                 contract_vars, level),
#          convert_formula_to_z3(formula.right_formula, contract_vars, level))
#     elif isinstance(formula, Disjunction):
#         return Or(convert_formula_to_z3(formula.left_formula,
#                                                     contract_vars, level),
#          convert_formula_to_z3(formula.right_formula, contract_vars, level))
#     elif isinstance(formula, Implication):
#         return Implies(convert_formula_to_z3(formula.left_formula,
#                                                         contract_vars, level),
#          convert_formula_to_z3(formula.right_formula, contract_vars, level))
#     elif isinstance(formula, Equivalence):
#         return (convert_formula_to_z3(formula.left_formula,
#                                                         contract_vars, level)
#          == convert_formula_to_z3(formula.right_formula, contract_vars, level))
#     else:
#         LOG.critical('incorrect unrolled formula')


class Z3Library(object):
    '''
    maps library to a set of integers
    '''


    def __init__(self, library, spec, library_max_redundancy=None, limit=None, context=None):
        '''
        associate library and create models.
        We need the spec, too, because we need to determine
        the number of replicate components we need.
        TODO
        There is a problem with the size of the library, though...
        '''
        self.library = library
        self.context = context
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
        self.relevant_models = {}

        #for bitvector map
        self.bitmap_comp_index = {}
        self.bitvect_repr = {}
        # self.model_bitmap = {}

        # self.unrolled_info = {}

        self.spec = spec

        # self.int_decl = []

        if library_max_redundancy is None:
            library_max_redundancy = DEFAULT_MAX_REDUNDANCY

        if limit is None:
            limit = len(spec.output_ports_dict)
        # LOG.debug(limit)
        # self.max_components = min([library_max_redundancy, limit])
        # self.max_num_components = self.max_components * len(self.library.components)


        self.max_components = {}

        elems = [component.cardinality if component.cardinality > 0 else min([library_max_redundancy, limit])
                 for component in self.library.components]
        self.max_num_components = sum(elems)

        comp_ind = 0b1

        for component in self.library.components:
            contract = component.contract

            self.contract_index[contract] = {}
            self.in_contract_index[contract] = {}
            self.out_contract_index[contract] = {}
            self.relevant_models[contract] = {}


            cardinality = component.cardinality
            if cardinality == 0:
                cardinality = min([library_max_redundancy, limit])

            self.max_components[contract] = cardinality

            for level in range(0, cardinality):

                self.contracts.add(contract)
                self.contract_index[contract][level] = []
                self.in_contract_index[contract][level] = []
                self.out_contract_index[contract][level] = []

                c_flag = Int('%s-%d' % (contract.base_name, level), self.context)
                self.contract_use_flags.append(c_flag)
                self.reverse_flag[c_flag.get_id()] = []
                self.flag_map['%s-%d' % (contract.base_name, level)] = c_flag

                #bitvector map
                self.bitmap_comp_index['%s-%d' % (contract.base_name, level)] = comp_ind #z3.BitVecVal(comp_ind,  self.max_num_components)

                self.bitvect_repr[comp_ind] = z3.BitVec("bitvar_"+str(comp_ind),  self.max_num_components, self.context)

                #shift one bit
                comp_ind = comp_ind << 1

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

                self.relevant_models[contract][level] = {}
                self.relevant_models[contract][level][0] = []
                self.relevant_models[contract][level][1] = []


                for port in contract.input_ports_dict.values():
                    model = z3.Int('%d-%s' % (level, port.unique_name), self.context)
                    # self.int_decl.append('(declare-const |%d-%s| Int)' % (level, port.unique_name))
                    self.models.append(model)
                    self.in_models.append(model)
                    self.ports.append(port)
                    self.in_ports.append(port)
                    self.model_levels[model.get_id()] = level
                    self.model_contracts[model.get_id()] = contract

                    if port not in self.index:
                        self.index[port] = {}
                        self.in_index[port] = {}

                    #bitvector map
                    #self.model_bitmap[model.get_id()] = z3.Bool('bit_%d-%s' % (level, port.unique_name))

                    #contract_indexing
                    self.contract_used_by_models[len(self.models) - 1] = c_flag
                    self.reverse_flag[c_flag.get_id()].append(len(self.models) -1)

                    #reverse lookup
                    self.model_index[model.get_id()] = len(self.models) - 1
                    self.model_in_index[model.get_id()] = len(self.models) - 1
                    self.index[port][level] = len(self.models) - 1
                    self.in_index[port][level] = len(self.in_models) - 1

                    self.contract_index[contract][level].append(len(self.models) - 1)
                    self.in_contract_index[contract][level].append(len(self.in_models) - 1)

                for port in contract.output_ports_dict.values():
                    model = z3.Int('%d-%s' % (level, port.unique_name), self.context)
                    # self.int_decl.append('(declare-const |%d-%s| Int)' % (level, port.unique_name))
                    self.models.append(model)
                    self.out_models.append(model)
                    self.ports.append(port)
                    self.out_ports.append(port)
                    self.model_levels[model.get_id()] = level
                    self.model_contracts[model.get_id()] = contract


                    if port not in self.index:
                        self.index[port] = {}
                        self.out_index[port] = {}

                    #bitvector map
                    #no need for outputs
                    #self.model_bitmap[model.get_id()] = z3.BitVec('bit_%d-%s' % (level, port.unique_name))

                    #contract_indexing
                    self.contract_used_by_models[len(self.models) - 1] = c_flag
                    self.reverse_flag[c_flag.get_id()].append(len(self.models) -1)

                    #reverse lookup
                    self.model_index[model.get_id()] = len(self.models) - 1
                    self.model_out_index[model.get_id()] = len(self.models) - 1
                    self.index[port][level] = len(self.models) - 1
                    self.out_index[port][level] = len(self.out_models) - 1

                    self.contract_index[contract][level].append(len(self.models) - 1)
                    self.out_contract_index[contract][level].append(len(self.out_models) - 1)


                (rel_in, rel_out) = self.__infer_relevant_ports(level, contract)

                self.relevant_models[contract][level][0] = rel_out
                self.relevant_models[contract][level][1] = rel_in

        # #add declarations for spec out
        # for name in self.spec.output_ports_dict:
        #     self.int_decl.append('(declare-const |%s| Int)' % name)



            # LOG.debug({i:self.models[i] for i in range(0,self.max_index)})


    def cast_to_context(self, context):
        '''
        translates all the models according to the new context
        :param context:
        :return:
        '''
        model_map = {model: model.translate(context) for model in self.models}
        index_map = {old.get_id(): new.get_id() for (old, new) in model_map.items()}

        in_model_map = {model: model.translate(context) for model in self.in_models}
        in_index_map = {old.get_id(): new.get_id() for (old, new) in in_model_map.items()}

        out_model_map = {model: model.translate(context) for model in self.out_models}
        outindex_map = {old.get_id(): new.get_id() for (old, new) in out_model_map.items()}

        contract_use_flags_map = {model: model.translate(context) for model in self.contract_use_flags}
        new_reverse_flag = {flag.get_id(): self.reverse_flag[flag] for flag in self.contract_use_flags}

        new_model_index = {index_map[mid]: self.model_index[mid] for mid in self.model_index}

    def include_spec_ports(self, spec_contract):
        '''
        assign an id also to spec_ids
        '''

        self.spec_contract = spec_contract
        self.spec_map = {}
        self.spec_by_index_map = {}
        m_index = len(self.models)

        for name, port in spec_contract.ports_dict.items():
            self.spec_map[name] = m_index
            self.spec_by_index_map[m_index] = name

            m_index = m_index + 1

        self.specs_at = len(self.models)
        self.positions = m_index


    def bitmap_component_index(self, contract, level):
        '''
        get the component index for bitmap
        :param contract:
        :param level:
        :return:
        '''
        return self.bitmap_comp_index['%s-%d' % (contract.base_name, level)]

    def bitmap_component_var(self, contract, level):
        '''
        get the component const for bitmap
        :param contract:
        :param level:
        :return:
        '''
        idx  = self.bitmap_comp_index['%s-%d' % (contract.base_name, level)]
        return self.bitvect_repr[idx]

    def __infer_relevant_ports(self, level, contract):
        """
        Return the list of relevant ports for a component.
        i.e., those ports that are involved in the evaluation of their spec
        :param level:
        :return:
        :param contract:
        :return:
        """

        # TODO: part of this is now implemented directly in contracts.
        # TODO: reimplement
        literals = (contract.assume_formula.get_literal_items()
                    | contract.guarantee_formula.get_literal_items())

        literal_unames = set([literal.unique_name for _, literal in literals])

        # match literals and ports
        ports = [port for port in contract.ports_dict.values() if port.unique_name in literal_unames]

        # LOG.debug(ports)

        ports_names = set([port.base_name for port in ports])
        in_models = [self.models[self.index[port][level]] for name, port in contract.input_ports_dict.items()
                     if name in ports_names]

        out_models = [self.models[self.index[port][level]] for name, port in contract.output_ports_dict.items()
                      if name in ports_names]

        return in_models, out_models


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
        return [self.contract_index[contract][level]
                for level in range(0, self.max_components[contract])]

    def contract_in_indices(self, contract):
        '''
        return all the input indices for a contract
        '''
        return [self.in_contract_index[contract][level]
                for level in range(0, self.max_components[contract])]

    def contract_out_indices(self, contract):
        '''
        return all the output indices for a contract
        '''
        # LOG.debug(hex(id(contract)))
        # LOG.debug(self.out_contract_index)
        return [self.out_contract_index[contract][level]
                for level in range(0, self.max_components[contract])]

    def port_by_model(self, model):
        '''
        returns the port given a model
        '''
        return self.ports[self.model_index[model.get_id()]]

    def model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return [self.models[self.index[port][level]]
                for level in range(0, self.max_components[port.contract])]

    def in_model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return [self.in_models[self.in_index[port][level]]
                for level in range(0, self.max_components[port.contract])]

    def out_model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return [self.out_models[self.out_index[port][level]]
                for level in range(0, self.max_components[port.contract])]

    def contract_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [[self.models[index]
                 for index in self.contract_index[contract][level]]
                for level in range(0, self.max_components[contract])]

    def contract_in_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [[self.in_models[index]
                 for index in self.in_contract_index[contract][level]]
                for level in range(0, self.max_components[contract])]

    def contract_out_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [[self.out_models[index]
                 for index in self.out_contract_index[contract][level]]
                for level in range(0, self.max_components[contract])]

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
                 for index in self.contract_index[contract][level]]

    def related_in_models(self, model):
        '''
        Given a model, finds all the models related to the same contract
        '''
        #infer level
        level = self.model_levels[model.get_id()]
        #get contract
        contract = self.model_contracts[model.get_id()]

        return [self.in_models[index]
                 for index in self.in_contract_index[contract][level]]

    def related_out_models(self, model):
        '''
        Given a model, finds all the models related to the same contract
        '''
        #infer level
        level = self.model_levels[model.get_id()]
        #get contract
        contract = self.model_contracts[model.get_id()]

        return [self.out_models[index]
                 for index in self.out_contract_index[contract][level]]

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

    def contract_by_index(self, index):
        '''
        returns contract and level associate to a model
        '''
        #infer mod
        model = self.model_by_index(index)
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
        # levels = [{} for _ in range(0, self.max_components)]
        levels = {}
        model_map_contract = {}
        contract_map = {}

        # for model in model_list:
        #     level, contract = self.contract_by_model(model)
        #     if contract not in levels[level]:
        #         levels[contract][level] = contract.copy()
        #
        #     model_map_contract[model.get_id()] = levels[contract][level]
        #     contract_map[(level, contract)] = levels[contract][level]

        for model in model_list:
            level, contract = self.contract_by_model(model)
            if contract not in levels:
                levels[contract] = {}
            if level not in levels[contract]:
                levels[contract][level] = contract.copy()

            model_map_contract[model.get_id()] = levels[contract][level]
            contract_map[(level, contract)] = levels[contract][level]


        return model_map_contract, contract_map

    def index_shift(self, index, shift_lev):
        '''
        returns the index shifted by shift_lev position.
        works as a circular buffer
        '''
        if index == -1:
            return -1

        # return (index + self.max_single_level_index * shift_lev) % self.max_index

        port = self.port_by_index(index)
        contract = port.contract
        mod = self.models[index]
        level = self.model_levels[mod.get_id()]

        shifted = (level + shift_lev) % self.max_components[contract]

        return self.index[port][shifted]


    def model_shift(self, model, shift_lev):
        '''
        returns the index shifted by shift_lev position.
        works as a circular buffer
        '''
        index = self.model_index[model.get_id()]

        return self.models[(index + self.max_single_level_index * shift_lev) % self.max_index]

    def index_in_shift(self, index, shift_lev):
        '''
        returns the index shifted by shift_lev position.
        works as a circular buffer
        '''
        if index == -1:
            return -1

        return (index + self.max_single_level_in_index * shift_lev) % self.max_in_index

    def relevant_input_models(self, level, contract):
        '''
        return relevant inputs
        :param level:
        :param contract:
        :return:
        '''

        return self.relevant_models[contract][level][1]

    def relevant_output_models(self, level, contract):
        '''
        return relevant outputs
        :param level:
        :param contract:
        :return:
        '''

        return self.relevant_models[contract][level][0]

    def relevant_input_indices(self, level, contract):
        '''
        return relevant inputs
        :param level:
        :param contract:
        :return:
        '''

        rel_in = self.relevant_input_models(level, contract)
        return [self.index_by_model(mod) for mod in rel_in]

    def relevant_output_indices(self, level, contract):
        '''
        return relevant outputs
        :param level:
        :param contract:
        :return:
        '''

        rel_out = self.relevant_output_models(level, contract)
        return [self.index_by_model(mod) for mod in rel_out]

    def flag_by_contract(self, level, contract):
        '''
        returns the flag associate to contract and level
        :param level:
        :param contract:
        :return:
        '''

        return self.flag_map['%s-%d' % (contract.base_name, level)]