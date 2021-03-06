'''
This module includes the interface classes and functions for the Z3 SMT solver

Author: Antonio Iannopollo
'''

# import logging
import itertools
from time import time

import types
from z3 import *

from pyco.contract import CompositionMapping, DummyType
from pyco import LOG
from pyco.z3_thread_manager import ModelVerificationManager, MAX_THREADS
from pyco.smt_factory import SMTModelFactory
from pyco.z3_library_conversion import Z3Library

# LOG = logging.getLogger()
LOG.debug('in z3_interface')


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
        # selfeset = library.typeset
        self.type_compatibility_set = library.type_compatibility_set
        self.max_hierarchy = library.max_hierarchy
        self.refined_by = library.refined_by
        self.refines = library.refines
        self.hierarchy = library.hierarchy

        # constraints by components
        self.distinct_ports_by_component = {}

        self.property_model = None
        self.property_contract = None
        self.specification_list = []
        self.num_out = 0
        # self.ComponentBaseName = None

        self.dummy_model_set = set()

        self.contracts_dict = {}
        # self.portc_types = {}
        # self.mapping_datatypes = {}
        # self.mapping_pairs = {}
        self.contract_model_instances = {}
        self.port_names = set()

        # TODO remember to include mapping
        self.component_refinement = None

        # hints from designer
        self.same_block_constraints = None
        self.distinct_mapping_constraints = None

        self.fixed_components = None
        self.fixed_connections = None
        self.fixed_connections_spec = None

        self.counter = itertools.count()
        self.port_dict = {}

        # maintain a list of contracts to check for consistency
        self.consistency_dict = {}

        self.solver = None
        self.max_components = None

    @property
    def extended_instances(self):
        '''
        returns library instances plus property model
        '''
        assert self.property_model is not None

        return dict(self.contract_model_instances.items() + [(self.property_model, self.property_contract)])

    def process_distinct_ports_by_component(self, library):
        '''
        add all the distinct ports constraints retrieved by library components
        '''

        for component in library.components:
            self.distinct_ports_by_component[component.contract] = component.distinct_set

    def initiliaze_solver(self, property_contract, limit, library_max_redundancy=None):
        '''
        Create environment and models from library
        '''

        port_name_pairs = self.library.smt_manager.port_name_pairs
        contract_name_pairs = self.library.smt_manager.contract_name_pairs
        component_name_pairs = self.library.smt_manager.component_name_pairs

        # extend port names with property ones
        _ = [port_name_pairs.append((port.base_name, port.unique_name))
             for port in property_contract.ports_dict.values()]

        # extends contract names
        contract_name_pairs.append((property_contract.base_name, property_contract.unique_name))

        # self.property_model = self.create_contract_model(property_contract, 0, is_library_elem=False)
        self.property_contract = property_contract

        self.create_z3_environment(self.property_contract, limit, library_max_redundancy)

    def create_z3_environment(self, spec, limit, library_max_redundancy=None):
        """
        Creates basic types for the current library instance
        """

        self.spec_out_dict = {name: z3.Int('%s' % name) for name in spec.output_ports_dict}
        self.spec_in_dict = {name: z3.Int('%s' % name) for name in spec.input_ports_dict}

        self.spec_dict = dict(self.spec_in_dict.items() + self.spec_out_dict.items())

        self.spec_outs = self.spec_out_dict.values()
        self.spec_ins = self.spec_in_dict.values()

        self.num_out = len(self.spec_outs)

        self.lib_model = Z3Library(self.library, spec, library_max_redundancy=library_max_redundancy, limit=limit)
        self.lib_model.include_spec_inputs(spec)

        # LOG.debug(self.lib_model.models_by_contracts())
        self.spec_ports = self.preprocess_specifications(self.specification_list)

        # get all the distinct ports contractints from components
        self.process_distinct_ports_by_component(self.library)

        # reorder specification list
        # LOG.debug(self.specification_list)
        self.specification_list = sorted(self.specification_list, key=lambda x: len(self.spec_ports[x][0]))
        # LOG.debug(self.specification_list)


        #init dummy set
        for p_model in self.spec_outs:
            name = str(p_model)
            if name not in self.specification_list[0].ports_dict:
                self.dummy_model_set.add(p_model.get_id())

        # self.solver = Solver()
        self.solver = Goal()  # Optimize()

        LOG.debug('ok')
        LOG.debug(self.lib_model)

    def preprocess_specifications(self, specifications):
        '''
        Finds what ports are actually necessary to evaluate the property.
        If they are a proper subset of the total set of ports, rejection of
        candidates could be more efficient
        '''

        spec_ports = {}

        for spec in specifications:
            spec_ports[spec] = {}

            literals = (spec.assume_formula.get_literal_items()
                        | spec.guarantee_formula.get_literal_items())

            literal_unames = set([literal.unique_name for _, literal in literals])

            # match literals and ports
            ports = [port for port in spec.ports_dict.values() if port.unique_name in literal_unames]

            # LOG.debug(ports)

            ports_names = set([port.base_name for port in ports])
            in_models = [s_mod for s_mod in self.spec_ins
                         if str(s_mod) in ports_names]

            out_models = [s_mod for s_mod in self.spec_outs
                          if str(s_mod) in ports_names]

            spec_ports[spec][0] = out_models
            spec_ports[spec][1] = in_models

        # LOG.debug(spec_ports)
        return spec_ports

    def use_n_components(self, n):
        '''
        Force the solver to use n components for a candidate solution
        '''

        constraints = []

        # limit the values
        constraints += [Or(comp == 0, comp == 1) for comp in self.lib_model.contract_use_flags]

        constraints += [Implies(flag == 1,
                                Or([Or([spec == index
                                        for index in self.lib_model.reverse_flag[flag.get_id()]]
                                       )
                                    for spec in self.spec_outs]))
                        for flag in self.lib_model.contract_use_flags]

        # zero otherwise
        constraints += [Implies(flag == 0,
                                And([And([spec != index
                                          for index in self.lib_model.reverse_flag[flag.get_id()]]
                                         )
                                     for spec in self.spec_outs]))
                        for flag in self.lib_model.contract_use_flags]

        constraints += [Sum(self.lib_model.contract_use_flags) == n]

        # LOG.debug(constraints)
        # self.solver.add(constraints)
        return constraints

    def use_max_n_components(self, n):
        '''
        Force the solver to use n components for a candidate solution
        '''

        constraints = []

        # limit the values
        constraints += [Or(comp == 0, comp == 1) for comp in self.lib_model.contract_use_flags]

        constraints += [Implies(flag == 1,
                                Or([Or([spec == index
                                        for index in self.lib_model.reverse_flag[flag.get_id()]]
                                       )
                                    for spec in self.spec_outs]))
                        for flag in self.lib_model.contract_use_flags]

        # zero otherwise
        constraints += [Implies(flag == 0,
                                And([And([spec != index
                                          for index in self.lib_model.reverse_flag[flag.get_id()]]
                                         )
                                     for spec in self.spec_outs]))
                        for flag in self.lib_model.contract_use_flags]

        constraints += [Sum(self.lib_model.contract_use_flags) <= n]

        # LOG.debug(constraints)
        # self.solver.add(constraints)
        return constraints

    def full_spec_out(self):
        '''
        all the outputs must be connected (-1 < spec < max)

        '''

        constraints = []
        constraints += [port > -1 for port in self.spec_outs]
        constraints += [port < self.lib_model.max_index for port in self.spec_outs]

        #but distinct.
        # constraints += [Distinct(self.spec_outs)]

        self.solver.add(constraints)

    def lib_full_chosen_output(self):
        '''
        All the outputs of chosen components must be connected to spec or inputs
        '''
        constraints = []

        for spec in self.spec_outs:
            for model in self.lib_model.out_models:
                index = self.lib_model.index_by_model(model)
                if_part = (spec == index)

                # get all inputs for model
                other_outs = self.lib_model.related_out_models(model)

                then_part = []
                for mod in other_outs:
                    i_mod = self.lib_model.index_by_model(mod)
                    if i_mod != index:
                        inner_part = []
                        # either connected to a spec
                        inner_part += [s_out == i_mod for s_out in self.spec_outs
                                       if s_out.get_id() != spec.get_id()]
                        # or another model
                        inner_part += [other_m == i_mod
                                       for other_m in self.lib_model.in_models
                                       if other_m.get_id() != model.get_id()]

                        if inner_part:
                            then_part.append(Or(inner_part))

                if then_part:
                    constraints.append(Implies(if_part, And(then_part)))

        # LOG.debug(constraints)
        if constraints:
            self.solver.add(constraints)

    def spec_out_to_out(self):
        '''
        a spec out can connect only to another output
        '''

        constraints = []
        # print self.lib_model.max_single_level_index
        # get all the duplicates
        constraints += [And([model != (index + self.lib_model.max_single_level_index * level)
                             for level in range(0, self.lib_model.max_components)
                             for index in range(0, self.lib_model.max_single_level_index)
                             if self.lib_model.port_by_index(index).is_input])
                        for model in self.spec_outs]

        # LOG.debug(constraints)

        self.solver.add(constraints)

    def full_spec_in(self):
        '''
        all the inputs must be connected (0 < spec < max),
        but distinct.

        '''

        constraints = []

        constraints += [Or([port == index
                            for port in self.lib_model.in_models])
                        for index in self.lib_model.spec_by_index_map.keys()]
        # constraints += [port > -1 for port in self.spec_ins]
        # constraints += [port < self.lib_model.max_index for port in self.spec_ins]
        # constraints += [Distinct(self.spec_ins)]

        self.solver.add(constraints)


    def lib_chosen_not_zeros(self):
        '''
        If a component is chosen, then its inputs ports are > -1.

        '''

        constraints = []

        #ALL ports <  self.lib_model.positions
        constraints += [And([model < self.lib_model.positions
                        for model
                        in self.lib_model.related_models(self.lib_model.model_by_index(index))])
                        for index in range(0, self.lib_model.max_index)]

        #inputs >-1 if connected
        constraints += [And([Implies(spec_port == index,
                                     And([model > -1
                                          for model
                                          in self.lib_model.related_in_models(self.lib_model.model_by_index(index))]))
                             for index in range(0, self.lib_model.max_index)])
                        for spec_port in self.spec_outs]


        self.solver.add(constraints)


    def lib_to_outputs_or_spec_in(self):
        '''
        a lib element can only be connected to an output or to a port selected as spec input

        '''

        constraints = []

        constraints += [And([model != (index + self.lib_model.max_single_level_index * level)
                             for level in range(0, self.lib_model.max_components)
                             for index in range(0, self.lib_model.max_single_level_index)
                             if self.lib_model.port_by_index(index).is_input])
                        for model in self.lib_model.in_models]

        # print constraints

        self.solver.add(constraints)

    def lib_chosen_to_chosen(self):
        '''
        Input of a chosen contract can be connected only to the output of a chosen contract,
        or a spec input
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
                        for level in range(0, self.lib_model.max_components)]

        # LOG.debug(constraints)

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
                        for level in range(0, self.lib_model.max_components)]

        self.solver.add(constraints)

    def spec_process_out_types(self):
        '''
        accept only connections for compatible types
        sub_types are assumed processed in type_compatibility_set
        '''

        constraints = []

        for s_name, s_mod in self.spec_out_dict.items():
            s_port = self.property_contract.ports_dict[s_name]
            s_port_type = self.property_contract.port_type[s_name]
            for index in range(0, self.lib_model.max_single_level_out_index):
                port = self.lib_model.out_ports[index]
                p_name = port.base_name
                contract = port.contract
                p_type = contract.port_type[p_name]
                if (
                        (not issubclass(p_type, s_port_type))):

                    for lev in range(0, self.lib_model.max_components):
                        constraints.append(s_mod != self.lib_model.index[lev][port])

        # LOG.debug(constraints)
        self.solver.add(constraints)

    def spec_process_in_types(self):
        '''
        accept only connections for compatible types
        sub_types are assumed processed in type_compatibility_set
        '''

        constraints = []

        for s_name, s_mod in self.spec_in_dict.items():
            s_port = self.property_contract.ports_dict[s_name]
            s_port_type = self.property_contract.port_type[s_name]
            for index in range(0, self.lib_model.max_single_level_in_index):
                port = self.lib_model.in_ports[index]
                p_name = port.base_name
                contract = port.contract
                p_type = contract.port_type[p_name]
                if (
                        # (not issubclass(s_port_type, p_type))):
                        # CHECK YOUR DEFINITION OF TYPE COMPATIBILITY
                        (not issubclass(p_type, s_port_type))):

                    for lev in range(0, self.lib_model.max_components):
                        constraints.append(self.lib_model.model_by_port(port)[lev] != self.lib_model.spec_map[s_name])

        LOG.debug(constraints)
        self.solver.add(constraints)

    def lib_process_types(self):
        '''
        accept only connections for compatible types
        sub_types are assumed processed in type_compatibility_set
        '''

        constraints = []

        for index in range(0, self.lib_model.max_single_level_in_index):
            in_port = self.lib_model.in_ports[index]
            in_mod = self.lib_model.in_models[index]
            in_name = in_port.base_name
            in_contract = in_port.contract
            in_port_type = in_contract.port_type[in_name]
            for o_index in range(0, self.lib_model.max_single_level_out_index):
                out_port = self.lib_model.out_ports[o_index]
                out_name = out_port.base_name
                out_contract = out_port.contract
                out_type = out_contract.port_type[out_name]

                if (
                                ((out_type, in_port_type)
                                 not in self.type_compatibility_set)
                            and
                                (out_type != in_port_type)
                        and
                            (not issubclass(out_type, in_port_type))):

                    for lev in range(0, self.lib_model.max_components):
                        for ind_l in range(0, self.lib_model.max_components):
                            ind = self.lib_model.index_in_shift(index, ind_l)
                            in_mod = self.lib_model.in_models[ind]
                            constraints.append(in_mod != self.lib_model.index[lev][out_port])

        # LOG.debug(constraints)
        self.solver.add(constraints)

    def compute_distinct_port_spec_constraints(self):
        '''
        computes the set of distinct ports according the info from the user
        '''

        constraints = []

        constraints += [self.spec_dict[name1] != self.spec_dict[name2]
                        for name1, name2 in self.distinct_mapping_constraints]

        self.solver.add(constraints)

    def compute_distinct_port_lib_constraints(self):
        '''
        computes the set of distinct ports according the info from the user
        '''

        constraints = []

        for contract in self.lib_model.contracts:
            for name1, name2 in self.distinct_ports_by_component[contract]:
                port1 = contract.ports_dict[name1]
                port2 = contract.ports_dict[name2]

                models_1 = self.lib_model.model_by_port(port1)
                models_2 = self.lib_model.model_by_port(port2)

                if port1.is_input and port2.is_input:
                    for level in range(0, self.lib_model.max_components):
                        constraints.append(Or(And(models_1[level] == -1,
                                                  models_2[level] == -1),
                                              models_1[level] != models_2[level]))
                elif port1.is_output and port2.is_input:
                    for level in range(0, self.lib_model.max_components):
                        constraints.append(models_2[level] != self.lib_model.index_by_model(models_1[level]))
                elif port1.is_input and port2.is_output:
                    for level in range(0, self.lib_model.max_components):
                        constraints.append(models_1[level] != self.lib_model.index_by_model(models_2[level]))
                else:
                    raise ValueError('cannot connect %s, %s ' % (port1.unique_name, port2.unique_name))

        # LOG.debug(constraints)
        self.solver.add(constraints)

    def compute_same_block_constraints(self):
        '''
        computes same block constraints according to the info given
        by the user
        '''

        constraints = []

        for name_a, name_b in self.same_block_constraints:
            # detect if out or inputs
            port_a = self.property_contract.ports_dict[name_a]
            port_b = self.property_contract.ports_dict[name_b]

            if port_a.is_output and port_b.is_output:
                constraints += [Or([And(self.spec_dict[name_a] == self.lib_model.index_by_model(port1),
                                        self.spec_dict[name_b] == self.lib_model.index_by_model(port2))
                                    for models in self.lib_model.models_by_contracts()
                                    for port1, port2 in itertools.permutations(models, 2)
                                    if self.lib_model.port_by_model(port1).is_output and
                                    self.lib_model.port_by_model(port2).is_output])]

            elif port_a.is_output and port_b.is_input:
                constraints += [Or([And(self.spec_dict[name_a] == self.lib_model.index_by_model(port1),
                                        port2 == self.lib_model.spec_map[name_b])
                                    for models in self.lib_model.models_by_contracts()
                                    for port1, port2 in itertools.permutations(models, 2)
                                    if self.lib_model.port_by_model(port1).is_output and
                                    self.lib_model.port_by_model(port2).is_input])]

            elif port_a.is_input and port_b.is_output:
                constraints += [Or([And(port1 == self.lib_model.spec_map[name_a],
                                        self.spec_dict[name_b] == self.lib_model.index_by_model(port2))
                                    for models in self.lib_model.models_by_contracts()
                                    for port1, port2 in itertools.permutations(models, 2)
                                    if self.lib_model.port_by_model(port1).is_input and
                                    self.lib_model.port_by_model(port2).is_output])]
            else:
                constraints += [Or([And(port1 == self.lib_model.spec_map[name_a],
                                        port2 == self.lib_model.spec_map[name_b])
                                    for models in self.lib_model.models_by_contracts()
                                    for port1, port2 in itertools.permutations(models, 2)
                                    if self.lib_model.port_by_model(port1).is_input and
                                    self.lib_model.port_by_model(port2).is_input])]

        # LOG.debug(constraints)
        self.solver.add(constraints)

    def compute_fixed_components(self):
        '''
        computes contraints for fixed components that need to be used
        '''

        constraints = []

        for (comp, level) in self.fixed_components:
            c_flag = self.lib_model.flag_map['%s-%d' % (comp.contract.base_name, level)]
            constraints += [c_flag == 1]

        # LOG.debug(constraints)
        self.solver.add(constraints)


    def compute_fixed_connections(self):
        '''
        computes contraints for fixed connections that need to be used
        '''

        constraints = []

        for (comp1, p_name1, level1, comp2, p_name2, level2) in self.fixed_connections:
            port1 = comp1.contract.ports_dict[p_name1]
            port2 = comp2.contract.ports_dict[p_name2]

            model1 = self.lib_model.model_by_port(port1)[level1]
            index1 = self.lib_model.index[level1][port1]
            model2 = self.lib_model.model_by_port(port2)[level2]
            index2 = self.lib_model.index[level2][port2]

            if port1.is_input and port2.is_output:
                constraints += [model1 == index2]
            elif port1.is_output and port2.is_input:
                constraints += [model2 == index1]
            elif port1.is_input and port2.is_input:
                constraints += [model1 == model2]
            else:
                raise ValueError('%s, %s are both outputs' % (p_name1, p_name2))

        LOG.debug(constraints)
        self.solver.add(constraints)

    def compute_fixed_spec_connections(self):
        '''
        computes contraints for fixed connections that need to be used
        '''

        constraints = []

        for (comp, p_name, level, spec_port_name) in self.fixed_connections_spec:
            port = comp.contract.ports_dict[p_name]
            spec_port = self.property_contract.ports_dict[spec_port_name]

            model = self.lib_model.model_by_port(port)[level]
            index = self.lib_model.index[level][port]


            if spec_port.is_input and port.is_input:
                spec_index = self.spec_map[spec_port_name]
                constraints += [model == spec_index]
            elif spec_port.is_output and port.is_output:
                spec_model = self.spec_out_dict[spec_port_name]
                constraints += [spec_model == index]
            else:
                raise ValueError('%s, %s cannot be connected' % (p_name, spec_port_name))

        # LOG.debug(constraints)
        self.solver.add(constraints)

    def compute_fixed_connections_spec(self):
        '''
        computes contraints for fixed connections that need to be used
        '''

        constraints = []

        for (comp, level) in self.fixed_components:
            c_flag = self.lib_model.flag_map['%s-%d' % (comp.contract.base_name, level)]
            constraints += [c_flag == 1]

        # LOG.debug(constraints)
        self.solver.add(constraints)

    def synthesize(self, property_contracts, limit=None,
                   library_max_redundancy=None,
                   strict_out_lib_map=False,
                   strict_in_spec_map=True,
                   use_types=True,
                   use_hints=True,
                   minimize_components=False,
                   minimize_ports=False,
                   minimize_cost=False,
                   same_block_constraints=None,
                   distinct_mapping_constraints=None,
                   fixed_components=None,
                   fixed_connections=None,
                   fixed_connections_spec=None):
        '''
        perform synthesis process
        '''
        if sum([minimize_components, minimize_ports, minimize_cost]) > 1:
            raise OptimizationError('Only one objective can be minimized')
        if minimize_cost:
            raise NotImplementedError('Custom cost not yet implemented')

        self.time = {}
        self.time['start'] = time()
        self.same_block_constraints = same_block_constraints
        self.distinct_mapping_constraints = distinct_mapping_constraints
        self.fixed_components = fixed_components
        self.fixed_connections = fixed_connections
        self.fixed_connections_spec = fixed_connections_spec

        self.specification_list = property_contracts

        optimize = minimize_components | minimize_ports | minimize_cost

        # let's pick a root
        # we assume all the specs have same interface
        property_contract = self.specification_list[0]
        prop_out = len(property_contract.output_ports_dict)

        if limit is None:
            self.max_components = prop_out
        else:
            self.max_components = limit

            if limit > prop_out:
                # augment spec with dummy types

                SpecClsCopy = type('SpecClsCopy', type(property_contract).__bases__, dict(type(property_contract).__dict__))

                for n in range(0, limit - prop_out):
                    SpecClsCopy.OUTPUT_PORTS.append(('%s_dummy_%d' % (property_contract.unique_name, n), DummyType))

                property_contract = SpecClsCopy('%s_c' % property_contract.base_name)

        self.initiliaze_solver(property_contract, limit=self.max_components, library_max_redundancy=library_max_redundancy)

        # property model has to be fully connected - always true
        # self.solver.add(self.fully_connected(self.property_model))

        # configure constraints for size
        size_constraints = {n: self.use_n_components(n) for n in range(1, self.num_out + 1)}

        t = Tactic('simplify')

        # self.all_zero()
        LOG.debug(property_contract)

        # self.solver.reset()

        # #the following 2 lines enable 1step unrolling of formula
        # #keep it disabled. it seems faster, and more efficient, without it.
        # #probably because of the size of the formula.
        # #(tested with 200 components (cav 9 spec example, redundancy set to 20))
        # unroll = self.lib_model.get_unrolled_equiv(self.specification_list)
        # self.solver.add(unroll)

        self.solver.add(self.use_max_n_components(self.max_components))

        self.full_spec_out()

        if strict_out_lib_map:
            self.lib_full_chosen_output() #
        self.spec_out_to_out()

        if strict_in_spec_map:
            self.full_spec_in() #

        self.lib_chosen_not_zeros()
        self.lib_to_outputs_or_spec_in()
        self.lib_chosen_to_chosen()
        self.lib_not_chosen_zero()

        if use_types:
            self.spec_process_in_types() ### remove for tests with no types
            self.spec_process_out_types() ###
            self.lib_process_types() ###
        if use_hints:
            self.compute_distinct_port_spec_constraints() ###
            self.compute_distinct_port_lib_constraints() ###
            self.compute_same_block_constraints() ###
            self.compute_fixed_components()
            self.compute_fixed_connections()
            self.compute_fixed_spec_connections()


        r = t.apply(self.solver)

        if optimize:
            solv = Optimize()
        else:
            solv = Solver()

        solv.add(r.as_expr())
        self.solver = solv

        if minimize_components:
            self.obj = self.solver.minimize(Sum(self.lib_model.contract_use_flags))

        if minimize_ports:
            #minimize ports used
            used_ports = [z3.Int('used_%d'%i) for i in range(len(self.lib_model.models))]
            self.solver.add([Or(used == 0, used == 1) for used in used_ports])
            self.solver.add([Implies(used_ports[i]==1, self.lib_model.models[i]>-1) for i in range(len(self.lib_model.models))])
            self.solver.add([Implies(used_ports[i]==0, self.lib_model.models[i]==-1) for i in range(len(self.lib_model.models))])

            self.obj = self.solver.minimize(z3.Sum(used_ports))

        # push size constraint
        # when popping, it is ok losing the counterexample
        # for a given size. (it does not apply to greater sizes)

        # initial_size = 1
        initial_size = self.max_components
        # self.solver.push()
        # self.solver.add(size_constraints[initial_size])

        # LOG.debug(self.lib_model.index)
        # LOG.debug(self.lib_model.models)
        models = self.lib_model.models_by_contracts()
        for model in models:
            LOG.debug('--')
            for elem in model:
                LOG.debug('%d -> %s', self.lib_model.index_by_model(elem), elem)
        # LOG.debug(self.lib_model.models_in_by_contracts())
        # LOG.debug(self.solver.assertions())

        size = initial_size
        if MAX_THREADS >= 1:
            thread_manager = ModelVerificationManager(self)

            try:
                (model, composition,
                 spec, contract_list) = thread_manager.synthesize(size_constraints, size)
            except NotSynthesizableError:
                raise
            else:
                LOG.info(model)
                for c in contract_list:
                    LOG.debug(c)
                LOG.info(spec)
                LOG.info(composition)
                return model, composition, spec, contract_list

                # return model, composition, spec, contract_list
        else:
            while True:
                try:
                    model = self.propose_candidate()
                except NotSynthesizableError as err:
                    if size < self.self.max_components:
                        LOG.debug('Synthesis for size %d failed. Increasing number of components...', size)
                        size = size + 1
                        self.solver.pop()
                        self.solver.push()
                        self.solver.add(size_constraints[size])
                    else:
                        raise err
                else:
                    try:
                        composition, spec, contract_list = self.verify_candidate(model)
                    except NotSynthesizableError as err:
                        LOG.debug("candidate not valid")
                    else:
                        LOG.info(model)
                        for c in contract_list:
                            LOG.debug(c)
                        LOG.info(self.property_contract)
                        LOG.info(composition)
                        return model, composition, spec, contract_list

    def propose_candidate(self):
        '''
        generate a model
        '''

        # LOG.debug('start solving')
        res = self.solver.check()
        # LOG.debug(self.solver.upper(self.obj))
        #LOG.debug(self.solver.lower(self.obj))
        # LOG.debug(res)
        if res == sat:
            # LOG.debug(self.solver.model())
            # LOG.debug('func eval')
            # LOG.debug(self.solver.model()[self.fully_connected])
            pass
        else:
            # LOG.debug(self.solver.proof())
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

    def verify_candidate(self, model):
        '''
        check if a candidate is valid or not.
        Here we need to:
        1) transform the model to a contract composition
        2) LEARN
            2a)
        '''

        # self.reject_candidate(model, candidates)
        state, composition, connected_spec, contract_inst, failed_spec = \
            self.check_all_specs(model)
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

    def check_all_specs(self, model):
        '''
        check if the model satisfies a number of specs, if provided
        '''
        composition = None
        connected_spec = None
        contract_inst = None
        failed_spec = None
        for spec in self.specification_list:
            composition, connected_spec, contract_inst = \
                self.build_composition_from_model(model, spec, complete_model=True)

            if not composition.is_refinement(connected_spec):
                LOG.debug('ref check done 1')
                failed_spec = spec
                return False, composition, connected_spec, contract_inst, failed_spec

            LOG.debug('ref check done 2')

        return True, composition, connected_spec, contract_inst, None

    def build_composition_from_model(self, model, spec, complete_model=True):
        '''
        builds a contract composition out of a model
        '''

        # contracts = set()
        spec_contract = spec.copy()

        # LOG.debug(spec_contract)

        # find all contracts from model
        # a set will help us remove duplicates
        # contracts = set()

        # get all the models, checking outputs
        models = [self.lib_model.model_by_index(model[port].as_long()) for port in self.spec_outs]

        # now we get all the contracts related.
        # by construction fetching only the outputs, we have the full set of contracts
        model_map, contract_map = self.lib_model.contract_copies_by_models(models)

        # LOG.debug(model_map)
        # LOG.debug(contract_map)

        contracts = set(model_map.values())
        # extended_contracts = dict(list(contracts) + [spec_contract])

        # start composition
        # c_set = contracts
        # c_set.add(contracts.values()[0])
        mapping = CompositionMapping(contracts)

        # start with spec
        for p_model in self.spec_outs:
            if p_model.get_id() not in self.dummy_model_set:
                #there might be dummie ports

                name = str(p_model)
                spec_port = spec_contract.ports_dict[name]

                index = model[p_model].as_long()
                i_mod = self.lib_model.models[index]
                level = self.lib_model.model_levels[i_mod.get_id()]
                orig_port = self.lib_model.port_by_index(index)

                other_contract_orig = orig_port.contract
                other_contract = contract_map[(level, other_contract_orig)]

                port = other_contract.ports_dict[orig_port.base_name]

                spec_contract.connect_to_port(spec_port, port)

        # connections among candidates
        non_zero_port_models = [p_model for p_model in self.lib_model.in_models
                                if model[p_model].as_long() > -1]

        processed_ports = set()
        for p_model in non_zero_port_models:
            level, old_contract = self.lib_model.contract_by_model(p_model)
            current_contract = contract_map[(level, old_contract)]
            old_port = self.lib_model.port_by_model(p_model)
            current_port = current_contract.ports_dict[old_port.base_name]
            other_index = model[p_model].as_long()

            if other_index < self.lib_model.max_index:
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
                spec_contract.connect_to_port(spec_port, current_port)

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
        root = contracts.pop()

        # c_set.add(root.copy())

        composition = root.compose(contracts, composition_mapping=mapping)

        # LOG.debug('-----------')
        # LOG.debug(root)
        # for contract in contracts:
        #    LOG.debug(contract)
        #
        # LOG.debug(composition)
        # LOG.debug(spec_contract)

        contracts.add(root)

        return composition, spec_contract, contracts

    # def reject_candidate(self, model, failed_spec):
    def reject_candidate(self, model):
        '''
        reject a model and its equivalents
        '''

        c_sets = {}


        for spec in self.spec_outs:
            index = model[spec].as_long()
            mod = self.lib_model.models[index]
            (level, contract) = self.lib_model.contract_by_model(mod)
            if (level, contract) not in c_sets:
                c_sets[(level, contract)] = {}
                # find all related models
                # in_models = self.lib_model.related_in_models(mod)
                # for mod in in_models:
                #    c_sets[(level, contract)][mod.get_id()] = (mod, model[mod].as_long())

            c_sets[(level, contract)][spec.get_id()] = (spec, index)

        size = len(c_sets)

        # create containers as nested lists
        # one per each c_set and n lists inside
        classes = []

        for (level, contract) in c_sets:
            s_class = []
            s_pairs = c_sets[(level, contract)].values()
            mods = self.lib_model.contract_in_models(contract)

            for l in xrange(0, self.lib_model.max_components):
                l_class = []
                shift = self.lib_model.max_components - level + l
                for pair in s_pairs:
                    if pair[0].get_id() not in self.dummy_model_set:
                        l_class.append([pair[0] == self.lib_model.index_shift(pair[1], shift)])
                for i in xrange(0, len(mods[l])):
                    m_class = []
                    if model[mods[level][i]].as_long() < self.lib_model.max_index:
                        for l2 in xrange(0, self.lib_model.max_components):
                            shift = self.lib_model.max_components - level + l2
                            m_class.append(mods[l][i] ==
                                           self.lib_model.index_shift(model[mods[level][i]].as_long(), shift))
                    else:
                        m_class.append(mods[l][i] == model[mods[level][i]].as_long())

                    l_class.append(m_class)
                s_class.append(l_class)
            classes.append(s_class)

        # size


        rej_formula = Not(
            And(
                [Or(
                    [And(
                        [Or(
                            [And(line) for line in m_class]
                        )
                         for m_class in l_class]
                    )
                     for l_class in s_class]
                )
                 for s_class in classes]
            )
        )

        # LOG.debug(rej_formula)

        # self.solver.add(rej_formula)
        return rej_formula

    def allow_hierarchy(self, hierarchy, candidate_list):
        '''
        Allows components with hierarchy less than or equal to hierarchy
        '''
        constraints = [self.ZContract.hierarchy(candidate) <= BitVecVal(hierarchy, 2)
                       for candidate in candidate_list]

        return constraints

    def check_for_consistency(self, model, candidates, contract_instances, spec_contract, z3_lock=None):
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

        # instantiate single contracts
        for candidate in candidates:
            c_m = model[candidate]
            c_m.__hash__ = types.MethodType(zcontract_hash, c_m)
            c_name = str(simplify(self.ZContract.base_name(c_m)))

            # get base instance
            contract = contract_instances[c_m]

            if c_name not in self.consistency_dict:
                self.consistency_dict[c_name] = {}

            # contracts[c_m] = contract

            for (port_name_a, port_name_spec) in (
                    itertools.product(contract.output_ports_dict,
                                      spec_contract.output_ports_dict)):

                with z3_lock:
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

                    # LOG.debug(self.consistency_dict)
                    self.consistency_dict[c_name][(port_name_a, port_name_spec)] = True

                    # reinstantiate a fresh copy of contract
                    LOG.debug('pre copy')
                    spec_contract = spec_contract.copy()
                    LOG.debug('post copy')
                    # spec model is the same for all specs

                    contract = type(self.contract_model_instances[c_m])(c_name)

                    port_a = contract.output_ports_dict[port_name_a]
                    port_spec = spec_contract.output_ports_dict[port_name_spec]

                    spec_contract.connect_to_port(port_spec, port_a)

                    c_mapping = CompositionMapping([spec_contract, contract])
                    # names
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
                        # add constraints also for the contracts which refines this one
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
        # LOG.debug('consistency constraints')
        # LOG.debug(constraints)
        return constraints

    def recall_not_consistent_constraints(self):
        '''
        to be called by sizes > 1.
        Load all the information related to inconsistent
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
                       if self.consistency_dict[c_name][(port_name_a, port_name_s)] == False
                       ]
        # LOG.debug(constraints)
        return constraints



SMTModelFactory.register(Z3Interface)


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

# instance a public interface
# Z3 = Z3Interface()
