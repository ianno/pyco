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

    def __init__(self, library):
        '''
        associate library
        '''
        self.library = library
        self.models = []
        self.ports = []
        self.index = {}
        self.contract_index = {}
        self.out_models = []
        self.out_ports = []
        self.out_index = {}
        self.out_contract_index = {}
        self.in_models = []
        self.in_ports = []
        self.in_index = {}
        self.in_contract_index = {}


        for component in self.library.components:
            contract = component.contract
            self.contract_index[contract] = []
            self.in_contract_index[contract] = []
            self.out_contract_index[contract] = []

            for port in contract.input_ports.values:
                model = z3.Int('%s' % port.unique_name)
                self.models.append(model)
                self.in_models.append(model)
                self.ports.append(port)
                self.in_ports.append(port)

                #reverse lookup
                self.index[port] = len(self.models) - 1
                self.in_index[port] = len(self.in_models) - 1

                self.contract_index[contract].append(len(self.models) - 1)
                self.in_contract_index[contract].append(len(self.in_models) - 1)

            for port in contract.output_ports.values:
                model = z3.Int('%s' % port.unique_name)
                self.models.append(model)
                self.out_models.append(model)
                self.ports.append(port)
                self.out_ports.append(port)

                #reverse lookup
                self.index[port] = len(self.models) - 1
                self.out_index[port] = len(self.out_models) - 1

                self.contract_index[contract].append(len(self.models) - 1)
                self.out_contract_index[contract].append(len(self.out_models) - 1)


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
        return self.contract_index[contract]

    def contract_in_indices(self, contract):
        '''
        return all the input indices for a contract
        '''
        return self.in_contract_index[contract]

    def contract_out_indices(self, contract):
        '''
        return all the output indices for a contract
        '''
        return self.out_contract_index[contract]

    def model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return self.models[self.index[port]]

    def in_model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return self.in_models[self.in_index[port]]

    def out_model_by_port(self, port):
        '''
        returns the model given a port
        '''
        return self.out_models[self.out_index[port]]

    def contract_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [self.models[index] for index in self.contract_index[contract]]

    def contract_in_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [self.in_models[index] for index in self.in_contract_index[contract]]

    def contract_out_models(self, contract):
        '''
        returns all models related to a contract
        '''
        return [self.out_models[index] for index in self.out_contract_index[contract]]


class Z3Interface(object):
    '''
    Interface class for the Z3 SMT solver.
    Extends the class SMTModelFactory
    '''

    def __init__(self, library):
        '''
        init
        '''

        #set_param(proof=True)
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


        self.property_model = self.create_contract_model(property_contract, 0, is_library_elem=False)
        self.property_contract = property_contract

        self.create_z3_environment(self.property_contract)


    def create_z3_environment(self, spec):
        '''
        Creates basic types for the current library instance
        '''

        self.spec_outs = {name: z3.Int('%s' % name) for name in spec.output_ports}
        self.spec_ins = {name: z3.Int('%s' % name) for name in spec.input_ports}


        self.solver = Solver()

    def initialize_for_fixed_size(self, size):
        '''
        Instantiate structures for a given size
        '''
        constraints = []

        #try:
        #    self.solver.pop()
        #except z3.Z3Exception as err:
        #    #LOG.debug(err)
        #    pass

        #new solver!
        self.solver = Solver()
        #start incremental. push
        self.solver.push()

        #self.contract_model_instances={}
        #for index in range(0, size):
        #    for component in self.library.components:
        #        self.create_component_model(component, index)

        self.contract_model_instances = {self.create_component_model(component,
                                                                    index):
                                         component.contract
                                         for component in self.library.components
                                         for index in range(size)}

        #initialize the solver functions
        #constraints += self.define_initial_constraints()
        print '1'
        constraints += self.quantified_initial_contraints()
        #constraints += self.define_initial_connections()
        print '2'
        constraints += self.define_initial_connections_fast()
        #constraints += self.quantify_initial_connections()

        print '3'
        #self.solver.push()
        self.solver.add(constraints)

    def create_port_model(self, port, is_library_elem=True):
        '''
        override from SMTModelFactory method
        '''

        #model = self.ZPort.port(getattr(self.PortBaseName, port.base_name),
        #                        getattr(self.PortUniqueName, port.unique))

        model = self.ZPort.port(getattr(self.PortBaseName, port.base_name))

        #if is_library_elem:
        #    self.port_models[port] = model

        return model

    def create_contract_model(self, contract, index, is_library_elem=True):
        '''
        override from SMTModelFactory method
        '''
        #TODO
        #get rid of the is_library_elem param
        #create port_list
        #input_list = self.ZPortList.bottom
        #output_list = self.ZPortList.bottom

        #for port in contract.input_ports_dict.values():
        #    z_port = self.create_port_model(port, is_library_elem)
            #input_list = self.ZPortList.node(z_port, input_list)

        #for port in contract.output_ports_dict.values():
        #    z_port = self.create_port_model(port, is_library_elem)
            #output_list = self.ZPortList.node(z_port, output_list)


        #declare ammissible names for each contract
        #it's ok to store this data now
        self.contracts_dict[contract.unique_name] = contract

        #dtype = z3.Datatype(contract.unique_name)
        #_ = [dtype.declare(port_base_name) for port_base_name in contract.ports_dict]
        #self.portc_types[contract] = dtype.create()


        #model = self.ZContract.contract(getattr(self.ContractBaseName,
        #                                        contract.base_name),
        #                                #getattr(self.ContractUniqueName,
        #                                #        contract.unique_name),
        #                                len(contract.input_ports_dict),
        #                                input_list,
        #                                len(contract.output_ports_dict),
        #                                output_list, 0,
        #                                self.counter.next())

        model = self.ZContract.contract(getattr(self.ContractBaseName,
                                                contract.base_name),
                                        #        self.hierarchy.get(contract.base_name, 0),
                                        #        index)
                                        BitVecVal(self.hierarchy.get(contract.base_name, 0),
                                                     2),
                                        BitVecVal(index, 8))


        #add hash
        model.__hash__ = types.MethodType(zcontract_hash, model)
        #add eq
        #model.__eq__ = types.MethodType(zcontract_eq, model)
        #if is_library_elem:
        #    self.contract_model_instances[model] = contract

        return model

    def create_component_model(self, component, index, is_library_elem=True):
        '''
        override from SMTModelFactory method
        '''
        #create contract list
        #c_list = self.ZContractList.bottom

        model = self.create_contract_model(component.contract, index, is_library_elem)

        #add constraints from component
        self.distinct_ports_by_component[model] = component.distinct_set

        return model


    def quantified_initial_contraints(self):
        '''
        Same as 'define intial contraints, but using quantifiers'
        '''
        constraints = []

        #define functions from scratch.
        #Since we are adding components for each n, we need to re-declare all the
        #function values. We could try to incrementally add constraints,
        #without recreating everything each time...

        #define structural properties:

        #The first loop defines the library, we cannot quantify

        #LOG.debug(self.extended_instances.items())

        extended_instances = self.extended_instances

        #for (model, contract) in extended_instances.items():
        #    for port_name in self.port_names:

         #       port_name_model = getattr(self.PortBaseName, port_name)


                #if port_name in contract.input_ports_dict:
                    #constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == True)
                    #constraints.append(self.port_is_input(port_name_model, model) == True)
                    #constraints.append(self.port_is_output(port_name_model, model) == False)
                #elif port_name in contract.output_ports_dict:
                    #constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == True)
                    #constraints.append(self.port_is_input(port_name_model, model) == False)
                    #constraints.append(self.port_is_output(port_name_model, model) == True)
                #else:
                    #constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == False)
                    #constraints.append(self.port_is_input(port_name_model, model) == False)
                    #constraints.append(self.port_is_output(port_name_model, model) == False)


        c_a, c_b = Consts('c_a c_b', self.ZContract)
        p_a, p_b = Consts('p_a p_b', self.PortBaseName)

        #all the inputs connected -> full_input
        #in_conn_conditions = [z3.Implies(self.port_is_input(p_a, c_a),
        #                                  self.port_is_connected(c_a, p_a)) for p_a in self.port_dict.values()]

        #condition = [z3.If(z3.And(in_conn_conditions),
        #                                   self.full_input(c_a),
        #                                   z3.Not(self.full_input(c_a))))

        #condition = [z3.If(z3.And([z3.Implies(self.port_is_input(p_a, c_a),
        #                                  self.port_is_connected(c_a, p_a))
        #                           for p_a in self.port_dict.values()]),
        #                           self.full_input(c_a),
        #                           z3.Not(self.full_input(c_a)))
        #            for c_a in extended_instances]
        
        #skip use of is_input
        condition = [If(And([self.port_is_connected(m_a, p_a)
                                   for n_a, p_a in self.port_dict.items()
                                   if n_a in c_a.input_ports_dict]),
                                   self.full_input(m_a),
                                   Not(self.full_input(m_a)))
                    for m_a, c_a in extended_instances.items()]

        constraints += condition



        #all outputs connectedf -> full_output
        #out_conn_conditions = z3.ForAll([p_a], z3.Implies(self.port_is_output(p_a, c_a),
        #                                              self.port_is_connected(c_a, p_a)))
        #condition = z3.ForAll([c_a], z3.If(out_conn_conditions,
        #                                   self.full_output(c_a),
        #                                   z3.Not(self.full_output(c_a))))
        #constraints.append(condition)

        #condition = [z3.If(z3.And([z3.Implies(self.port_is_output(port, contract),
        #                                      self.port_is_connected(contract, port))
        #                           for port in self.port_dict.values()]),
        #                   self.full_output(contract),
        #                   z3.Not(self.full_output(contract)))
        #             for contract in extended_instances]

        #skip use of is_output
        condition = [If(And([self.port_is_connected(m_a, p_a)
                                   for n_a, p_a in self.port_dict.items()
                                   if n_a in c_a.output_ports_dict]),
                           self.full_output(m_a),
                           Not(self.full_output(m_a)))
                     for m_a, c_a in extended_instances.items()]
        constraints += condition

        #all inputs and all outputs -> fully connected
        #condition = z3.ForAll([c_a], z3.If(z3.And(self.full_input(c_a),
        #                                          self.full_output(c_a)),
        #                                   self.fully_connected(c_a),
        #                                   z3.Not(self.fully_connected(c_a))))
        #constraints.append(condition)

        condition = [If(And(self.full_input(contract),
                                  self.full_output(contract)),
                           self.fully_connected(contract),
                           Not(self.fully_connected(contract)))
                     for contract in extended_instances]

        constraints += condition

        #at least a connection -> port connected
        #condition = z3.ForAll([c_a, p_a], z3.If(z3.And(self.contract_has_port_wbase_name(c_a, p_a),
        #                                               z3.Exists([c_b, p_b],
        #                                                         #self.connected_ports(c_a, c_b,
        #                                                         #                     p_a, p_b)
        #                                                         z3.And(self.connected_ports(c_a, c_b,
        #                                                                              p_a, p_b),
        #                                                                z3.Or(z3.Distinct([c_a, c_b]),
        #                                                                      z3.Distinct([p_a, p_b]))
        #                                                                )
        #                                                         )
        #                                               ),
        #                                        self.port_is_connected(c_a, p_a),
        #                                        z3.Not(self.port_is_connected(c_a, p_a))
        #                                        )
        #                     )
        #constraints.append(condition)

        #condition = [z3.If(z3.And(self.contract_has_port_wbase_name(contract, port),
        #                           z3.Or([z3.And(self.connected_ports(contract, contract1,
        #                                                              port, port1),
        #                                         z3.Or(z3.Not(contract == contract1),
        #                                               z3.Not(port == port1)))
        #                                  for port1 in self.port_dict.values()
        #                                  for contract1 in extended_instances]
        #                                )
        #                           ),
        #                    self.port_is_connected(contract, port),
        #                    z3.Not(self.port_is_connected(contract, port)))
        #             for port in self.port_dict.values() for contract in extended_instances]
        
        #rewrite with less SMT functions
        condition = [If(Or([self.connected_ports(model, model1,
                                                                      port, port1)                                  for name1, port1 in self.port_dict.items()
                                  for model1, contract1 in extended_instances.items()
                                  if name1 in contract1.ports_dict and
                                     (contract1 != contract or name != name1)]
                                        ),
                            self.port_is_connected(model, port),
                            Not(self.port_is_connected(model, port)))
                     for name, port in self.port_dict.items()
                     for model, contract in extended_instances.items()
                     if name in contract.ports_dict]

        constraints += condition

        c_a, c_b = Consts('c_a c_b', self.ZContract)
        p_a, p_b = Consts('p_a p_b', self.PortBaseName)
        c_c = Const('c_c', self.ZContract)
        p_c = Const('p_c', self.PortBaseName)

        #connected_ports is symmetric
        #condition = z3.ForAll([c_a, c_b, p_a, p_b],
        #                      (self.connected_ports(c_a, c_b, p_a, p_b) ==
        #                       self.connected_ports(c_b, c_a, p_b, p_a)))
        #constraints.append(condition)


        #connected_ports is also transitive
        condition = ForAll([c_a, c_b, c_c, p_a, p_b, p_c],
                              Implies(And(self.connected_ports(c_a, c_b, p_a, p_b),
                                                self.connected_ports(c_b, c_c, p_b, p_c)),
                                         self.connected_ports(c_a, c_c, p_a, p_c)
                                        )
                             )
        constraints.append(condition)


        # SLOWER  
        #condition = [z3.Implies(z3.And(self.connected_ports(c_a, c_b, self.port_dict[p_a],
        #                                                    self.port_dict[p_b]),
        #                               self.connected_ports(c_b, c_c, self.port_dict[p_b],
        #                                                        self.port_dict[p_c])),
        #                        self.connected_ports(c_a, c_c, self.port_dict[p_a],
        #                            self.port_dict[p_c])
        #                       )
        #             for c_a, cc_a in self.extended_instances.items()
        #             for c_b, cc_b in self.extended_instances.items()
        #             for c_c, cc_c in self.extended_instances.items()
        #             for p_a in cc_a.ports_dict for p_b in cc_b.ports_dict
        #             for p_c in cc_c.ports_dict ]

        #constraints += condition

        #connected
        #condition = z3.ForAll([c_a, c_b],
        #                      z3.If(z3.Exists([p_a, p_b],
        #                                      self.connected_ports(c_a, c_b, p_a, p_b),
        #                                      ),
        #                            self.connected(c_a, c_b) == True,
        #                            self.connected(c_a, c_b) == False,
        #                            )
        #                      )
        #constraints.append(condition)

        #connected_output
        #condition = z3.ForAll([c_a, c_b],
        #                      z3.If(z3.Exists([p_a, p_b],
        #                                      z3.And(self.connected_ports(c_a, c_b, p_a, p_b),
        #                                             self.port_is_output(p_a, c_a),
        #                                             self.port_is_output(p_b, c_b)
        #                                            )
        #                                      ),
        #                            self.connected_output(c_a, c_b) == True,
        #                            self.connected_output(c_a, c_b) == False,
        #                            )
        #                      )
        #constraints.append(condition)


        return constraints

    def define_initial_connections_fast(self):
        '''
        A version of define_initial_connections using list comprehension
        Two outputs cannot be connected. Ports not related to contracts, cannot be connected
        Connections are transitive and symmetric
        '''
        constraints = []

        extended_instances = self.extended_instances
        product_f = itertools.product

        #p_model_pairs = itertools.product(self.port_dict.values(), repeat=2)
        #c_model_pairs = itertools.product(extended_instances, repeat=2)

        #symmetric
        #symmetric = lambda m_a,m_b,p_a,p_b: self.connected_ports(m_a, m_b, p_a, p_b) == self.connected_ports(m_b, m_a, p_b, p_a)

        #disconnected
        #disc = lambda m_a,m_b,p_a,p_b: z3.Not(self.connected_ports(m_a, m_b, p_a, p_b))

        #connected
        #conn = lambda m_a,m_b,p_a,p_b: self.connected_ports(m_a, m_b, p_a, p_b)

        print '2.1'

        constraints += [self.connected_ports(m_a, m_b, p_a, p_b) ==
                                   self.connected_ports(m_b, m_a, p_b, p_a)
                        for p_a, p_b in product_f(self.port_dict.values(), repeat=2)
                        for m_a, m_b in product_f(extended_instances, repeat=2)
                        ]



        #constraints += [self.connected_ports(m_a, m_b, self.port_dict[n_a],
        #                                    self.port_dict[n_b]) ==
        #                           self.connected_ports(m_b, m_a, self.port_dict[n_b],
        #                                                self.port_dict[n_a])
        #                for m_a, c_a in extended_instances.items()
        #                for m_b, c_b in extended_instances.items()
        #                for n_a in c_a.output_ports_dict
        #                for n_b in c_b.output_ports_dict
        #                ]

        print '2.2'

        #constraints += list(chain_f((symmetric(m_a, m_b, p_a, p_b),
        #                            conn_stat(m_a, c_a, m_b, c_b,
        #                                           p_name_a, p_a, p_name_b, p_b))
        #                for (p_name_a, p_a), (p_name_b, p_b)
        #                    in itertools.product(self.port_dict.items(), repeat=2)
        #                for (m_a, c_a), (m_b, c_b)
        #                    in itertools.product(extended_instances.items(), repeat=2)
        #                ))


        #since we use cartesian product,
        #simmetricity of connected_ports is implicit
        constraints += [Not(self.connected_ports(m_a, m_b, p_a, p_b))
                        if (p_name_a not in c_a.ports_dict) or
                             (p_name_b not in c_b.ports_dict)
                        else (
                            self.connected_ports(m_a, m_b, p_a, p_b)
                            if is_true(simplify(m_a == m_b)) and
                                is_true(simplify(p_a == p_b))
                            else (
                                Not(self.connected_ports(m_a, m_b, p_a, p_b))
                                if (is_false(simplify(m_a == self.property_model)) and
                                    is_false(simplify(m_b == self.property_model)) and
                                    (p_name_a in c_a.output_ports_dict) and
                                    (p_name_b in c_b.output_ports_dict))
                                else True #z3.Z3_OP_TRUE
                                 )
                        )
                        for (p_name_a, p_a), (p_name_b, p_b)
                            in itertools.product(self.port_dict.items(), repeat=2)
                        for (m_a, c_a), (m_b, c_b)
                            in itertools.product(extended_instances.items(), repeat=2)
                        ]



        print '2.3'
        #constraints.append(z3.If(z3.Or([self.connected_ports(m_a, m_b, p_a, p_b)
        #                                for p_a, p_b in product_f(self.port_dict.values(), repeat=2)
        #                                for m_a, m_b in product_f(extended_instances, repeat=2)
        #                            ]),
        #                             self.connected(m_a, m_b)==True,
        #                             self.connected(m_a, m_b)==False)
        #                   )

        #constraints.append(self.connected(m_a, m_b) == self.connected(m_b, m_a))

        #output_connection
        #constraints.append(self.connected_output(m_a, m_b) == self.connected_output(m_b, m_a))

        print '2.4'
        #constraints.append(z3.If(z3.Or([z3.And(self.connected_ports(m_a, m_b,
        #                                                           p_a, p_b),
        #                                   self.port_is_output(p_a, m_a),
        #                                   self.port_is_output(p_b, m_b))
        #                                for p_a, p_b in product_f(self.port_dict.values(), repeat=2)
        #                                for m_a, m_b in product_f(extended_instances, repeat=2)
        #                               ]),
        #                             self.connected_output(m_a, m_b) == True,
        #                             self.connected_output(m_a, m_b) == False
        #                             )
        #                      )

        #uses less functions
        #constraints += [z3.If(z3.Or([self.connected_ports(m_a, m_b,
        #                                                    self.port_dict[n_a],
        #                                                    self.port_dict[n_b])
        #                                for n_a in c_a.output_ports_dict
        #                                for n_b in c_b.output_ports_dict
        #                            ]),
        #                             self.connected_output(m_a, m_b) == True,
        #                             self.connected_output(m_a, m_b) == False
        #                             )
        #                for m_a, c_a in extended_instances.items()
        #                for m_b, c_b in extended_instances.items()
        #                ]

        print '2.5'
        return constraints

    def define_initial_connections(self):
        '''
        Two outputs cannot be connected. Ports not related to contracts, cannot be connected
        Connections are transitive and symmetric
        '''
        constraints = []

        extended_instances = self.extended_instances
        product_f = itertools.product
        #loop over all the possible instances
        #NOT considering the spec   
        #for (m_a, m_b) in itertools.permutations(self.extended_instances.keys(), 2):
        for (m_a, c_a), (m_b, c_b) in product_f(extended_instances.items(), repeat=2):
            #c_a = self.contract_model_instances[m_a]
            #c_b = self.contract_model_instances[m_b]
            #c_a = extended_instances[m_a]
            #c_b = extended_instances[m_b]

            #sub_constr_and = []
            sub_constr = []
            conn_out_constr = []
            diff_model = []

            #LOG.debug('iteration')
            for (p_a, p_a_model), (p_b, p_b_model) in product_f(self.port_dict.items(), repeat=2):
            #for item in itertools.combinations_with_replacement(set(self.port_names), 2):

                #LOG.debug(item)
                #(p_a, p_b) = item
                #p_a_model = getattr(self.PortBaseName, p_a)
                #p_b_model = getattr(self.PortBaseName, p_b)

                #if a is connected to b, then b is connected to a and vice versa
                #symmetric
                constraints.append(self.connected_ports(m_a, m_b, p_a_model, p_b_model) ==
                                   self.connected_ports(m_b, m_a, p_b_model, p_a_model))

                #used in implication, later, but only if not the same component and port
                sub_constr.append(self.connected_ports(m_a, m_b, p_a_model, p_b_model))
                conn_out_constr.append(And(self.connected_ports(m_a, m_b,
                                                                   p_a_model, p_b_model),
                                           self.port_is_output(p_a_model, m_a),
                                           self.port_is_output(p_b_model, m_b)))
                #LOG.debug('test-----------')
                #LOG.debug(m_a)
                #LOG.debug(m_b)
                #LOG.debug(p_a)
                #LOG.debug(p_b)
                #LOG.debug(z3.is_true(z3.simplify(m_a == self.property_model)))

                if (p_a not in c_a.ports_dict) or (p_b not in c_b.ports_dict):
                    #LOG.debug('1')
                    constraints.append(Not(self.connected_ports(m_a, m_b, p_a_model, p_b_model)))
                #connected_port is reflexive - but never in the case without replacement, or product
                elif (is_true(simplify(m_a == m_b)) and
                     is_true(simplify(p_a_model == p_b_model))):
                    #LOG.debug('2')
                    constraints.append(self.connected_ports(m_a, m_b, p_a_model, p_b_model))

                elif (is_false(simplify(m_a == self.property_model)) and
                        is_false(simplify(m_b == self.property_model))
                       and (p_a in c_a.output_ports_dict) and (p_b in c_b.output_ports_dict)):
                #elif (p_a in c_a.output_ports_dict) and (p_b in c_b.output_ports_dict):
                    #no connections between outputs of library elements
                    #LOG.debug('no output-----------')
                    #LOG.debug(m_a)
                    #LOG.debug(m_b)
                    #LOG.debug(p_a)
                    #LOG.debug(p_b)
                    constraints.append(Not(self.connected_ports(m_a, m_b, p_a_model, p_b_model)))
                    #pass

            #two contracts connected if there is at least a common connection
            #constraints.append(z3.Implies(z3.Not(z3.Or(sub_constr)), self.connected(m_a, m_b) == False))
            #constraints.append(z3.Implies(z3.Or(sub_constr), self.connected(m_a, m_b) == True))
            constraints.append(If(Or(sub_constr),
                                     self.connected(m_a, m_b)==True,
                                     self.connected(m_a, m_b)==False))
            
            constraints.append(self.connected(m_a, m_b) == self.connected(m_b, m_a))

            #output_connection
            constraints.append(self.connected_output(m_a, m_b) == self.connected_output(m_b, m_a))
            #constraints.append(z3.Implies(z3.Not(z3.Or(conn_out_constr)),
            #                              self.connected_output(m_a, m_b) == False))
            #constraints.append(z3.Implies(z3.Or(conn_out_constr),
            #                              self.connected_output(m_a, m_b) == True))
            constraints.append(If(Or(conn_out_constr),
                                     self.connected_output(m_a, m_b) == True,
                                     self.connected_output(m_a, m_b) == False
                                     )
                              )

        return constraints



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


    def all_models_completely_connected(self, candidate_models):
        '''
        All ports need to be connected
        '''

        constraints = [self.fully_connected(model) for model in candidate_models]

        return constraints

    def models_disconnected_if_not_solution(self, candidate_models):
        '''
        if not part of solution, everything disconnected
        '''
        constraints = []
        part1 = {}

        constraints = [Implies(Not(Or([m_a == candidate
                                                for candidate in candidate_models])),
                                  And([Not(self.port_is_connected(m_a, p_a))
                                          for (p_name, p_a) in self.port_dict.items()
                                          if p_name in c_a.ports_dict]))
                       for (m_a, c_a) in self.contract_model_instances.items()]

        return constraints

    def property_inputs_no_on_candidate_outputs(self):
        '''
        property inputs cannot be connected to models outputs
        '''

        constraints = [Not(self.connected_ports(self.property_model, m_b, p_p, p_b))
                        for n_p, p_p in self.port_dict.items()
                        if n_p in self.property_contract.input_ports_dict
                        for n_b, p_b in self.port_dict.items()
                        for m_b, c_b in self.extended_instances.items()
                        if n_b in c_b.output_ports_dict]

        return constraints

    def property_inputs_to_candidates(self):
        '''
        property inputs have to  be connected to models inputs
        '''

        constraints = [Or([self.connected_ports(self.property_model, m_b,
                                                          p_p, p_b)
                               for n_b, p_b in self.port_dict.items()
                               for m_b, c_b in self.contract_model_instances.items()
                               if n_b in c_b.input_ports_dict
                              ])
                        for n_p, p_p in self.port_dict.items()
                        if n_p in self.property_contract.input_ports_dict
                      ]

        return constraints

    def property_outputs_to_candidates(self):
        '''
        property outputs have to  be connected to models outputs
        '''

        constraints = [Or([self.connected_ports(self.property_model, m_b,
                                                          p_p, p_b)
                               for n_b, p_b in self.port_dict.items()
                               for m_b, c_b in self.contract_model_instances.items()
                               if n_b in c_b.output_ports_dict
                              ])
                        for n_p, p_p in self.port_dict.items()
                        if n_p in self.property_contract.output_ports_dict
                      ]

        return constraints

    def property_outputs_not_together(self):
        '''
        Output ports of property can be connected to other outputs, but not only
        among themselves
        '''
        constraints = []

        #TODO: refactor as list comprehension

        #do not consider the same port twice e.g. (a, a): in that case reflexivity guarantees
        #the property to be true
        for (p_a, p_b) in itertools.combinations(self.property_contract.output_ports_dict.keys(), 2):
            port_model_a = getattr(self.PortBaseName, p_a)
            port_model_b = getattr(self.PortBaseName, p_b)

            constraints.append(self.connected_ports(self.property_model,
                                                    self.property_model,
                                                    port_model_a,
                                                    port_model_b)==False)

        return constraints

    def inputs_on_property_inputs_or_candidate_out(self, candidates):
        '''
        An input of a candidate can be only connected to inputs of the
        property or to an output of any candidate
        '''

        constraints = [And([Implies(cand == m_a,
                                  Or([self.connected_ports(m_a, m_b, p_a, p_b)
                                    for n_b, p_b in self.port_dict.items()
                                    for m_b, c_b in self.contract_model_instances.items()
                                    if n_b in c_b.output_ports_dict
                                    ] +
                                    [self.connected_ports(m_a, self.property_model, p_a, p_b)
                                    for n_b, p_b in self.port_dict.items()
                                    if n_b in self.property_contract.input_ports_dict
                                    ])
                                    )
                                for n_a, p_a in self.port_dict.items()
                                for m_a, c_a in self.contract_model_instances.items()
                                if n_a in c_a.input_ports_dict
                              ])
                        for cand in candidates]

        return constraints

    def property_ports_controlled_by_same_component(self, port_name_a, port_name_b):
        '''
        Specify that property ports port_name_a and b are controlled
        by the same component
        '''
        port_a = getattr(self.PortBaseName, port_name_a)
        port_b = getattr(self.PortBaseName, port_name_b)

        constraints = Or([And(self.connected_ports(self.property_model, m_a,
                                                         port_a, p_x),
                                    self.connected_ports(self.property_model, m_a,
                                                         port_b, p_y))
                        for p_name_x, p_x in self.port_dict.items()
                        for p_name_y, p_y in self.port_dict.items()
                        for m_a, c_a in self.contract_model_instances.items()
                        if p_name_x in c_a.ports_dict and p_name_y in c_a.ports_dict])

        return constraints

    def compute_same_block_constraints(self):
        '''
        computes same block constraints according to the info given
        by the user
        '''
        constraints = [self.property_ports_controlled_by_same_component(name_a, name_b)
                        for name_a, name_b in self.same_block_constraints]

        return constraints

    #def map_property_ports_on_distinct_ports(self, port_name_a, port_name_b):
    #    '''
    #    prevents two ports of the property to be mapped on the same candidate port
    #    '''
    #    port_a = getattr(self.PortBaseName, port_name_a)
    #    port_b = getattr(self.PortBaseName, port_name_b)
    #
    #    constraints = z3.And([z3.Not(self.connected_ports(self.property_model,
    #                                                             m_x, port_a, p_x))
    #                         for name_x, p_x in self.port_dict.items()
    #                         for m_x, c_x in self.contract_model_instances.items()
    #                         if name_x in c_x.ports_dict])
    #    #LOG.debug(constraints)
    #    return constraints

    def compute_distinct_port_constraints(self):
        '''
        computes the set of distinct ports according the info from the user
        '''

        #constraints = [self.map_property_ports_on_distinct_ports(name_a, name_b)
        #               for name_a, name_b in self.distinct_mapping_constraints]
        constraints = [Not(self.connected_ports(self.property_model,
                                                   self.property_model,
                                                   self.port_dict[name_a],
                                                   self.port_dict[name_b])
                              )
                        for name_a, name_b in self.distinct_mapping_constraints]

        return constraints


    def process_candidate_type_compatibility(self):
        '''
        Prevents connections among incompatible types.
        OK only if inputs are connected and with same type
        or if an input gets fed by a subtype
        '''

        constraints = [Not(self.connected_ports(m_a, m_b, p_a, p_b))
                        for p_name_a, p_a in self.port_dict.items()
                        for p_name_b, p_b in self.port_dict.items()
                        for m_a, c_a in self.contract_model_instances.items()
                        for m_b, c_b in self.contract_model_instances.items()
                        if p_name_a in c_a.ports_dict and
                           p_name_b in c_b.ports_dict and
                           (
                            ((c_a.port_type[p_name_a], c_b.port_type[p_name_b]) not in
                           self.type_compatibility_set) and
                            (c_a.port_type[p_name_a] != c_b.port_type[p_name_b]) and 
                            (p_name_a in c_a.input_ports_dict and
                             p_name_b in c_b.output_ports_dict and not
                             issubclass(c_b.port_type[p_name_b], c_a.port_type[p_name_a])) or
                            (p_name_a in c_a.output_ports_dict and
                             p_name_b in c_b.input_ports_dict and not
                             issubclass(c_a.port_type[p_name_a], c_b.port_type[p_name_b]))
                            )]
        #LOG.debug(constraints)
        return constraints

    def process_spec_type_compatibility(self):
        '''
        Allows spec to be connected only to similar types
        '''

        constraints = [Not(self.connected_ports(self.property_model, m_b, p_a, p_b))
                        for p_name_a, p_a in self.port_dict.items()
                        for p_name_b, p_b in self.port_dict.items()
                        for m_b, c_b in self.contract_model_instances.items()
                        if p_name_a in self.property_contract.ports_dict and
                           p_name_b in c_b.ports_dict and
                           not issubclass(c_b.port_type[p_name_b],
                                          self.property_contract.port_type[p_name_a])]
        #LOG.debug(constraints)
        return constraints


    def compute_component_port_constraints(self):
        '''
        Adds constraints (distinct ports) taken from library components
        '''


        constraints = [Not(self.connected_ports(m_a, m_a,
                                                   self.port_dict[name_a],
                                                   self.port_dict[name_b])
                             )
                             for m_a, port_set in self.distinct_ports_by_component.items()
                             for name_a, name_b in port_set
                       ]
        #LOG.debug(constraints)
        return constraints


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

        for size_n in range(1, max_components+1):
            try:
                candidate, composition, spec, c_list = self.synthesize_fixed_size(size_n)
            except NotSynthesizableError:
                LOG.debug("size %d synthesis failed" % size_n)
            else:
                LOG.debug(candidate)
                LOG.debug(composition)
                LOG.debug(spec)
                LOG.debug(self.time)
                return candidate, composition, spec, c_list

        raise NotSynthesizableError

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

    def propose_candidate(self, size):
        '''
        generate a model
        '''
        #z3.set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)
        #LOG.debug(self.solver.assertions)

        LOG.debug('start solving')
        res = self.solver.check()
        LOG.debug(res)
        LOG.debug('done')
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

        return model



    def verify_candidate(self, model, candidates):
        '''
        check if a candidate is valid or not.
        Here we need to:
        1) transform the model to a contract composition
        2) LEARN
            2a)
        '''

        #self.reject_candidate(model, candidates)
        state, composition, connected_spec, contract_inst = \
                self.check_all_specs(model, candidates)
        if not state:
            #learn
            #as first step, we reject the actual solution
            #self.solver.add(self.exclude_candidate_type())
            #LOG.debug('exclude')
            #LOG.debug(z3.Not(self.connected_ports==model[self.connected_ports]))
            #self.solver.add(z3.Not(self.connected_ports==model[self.connected_ports]))
            self.solver.add(self.reject_candidate(model, candidates))

            #then check for consistency
            self.solver.add(self.check_for_consistency(model, candidates, contract_inst, connected_spec))

            raise NotSynthesizableError

        return composition, connected_spec, contract_inst

    def check_all_specs(self, model, candidates):
        '''
        check if the model satisfies a number of specs, if provided
        '''
        composition = None
        connected_spec = None
        contract_inst = None
        for spec in self.specification_list:
            composition, connected_spec, contract_inst = \
                    self.build_composition_from_model(model, spec, candidates, complete_model=True)

            LOG.debug('ref check')
            if not composition.is_refinement(connected_spec):
                LOG.debug('ref check done 1')
                return False, composition, connected_spec,contract_inst

            LOG.debug('ref check done 2')

        return True, composition, connected_spec,contract_inst



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

    def reject_candidate(self, model, candidates):
        '''
        I'm so sorry, but we need efficiency...if any
        reject proposed solution.
        we have a set of contracts, and a set of functions.
        We can reject the actual evaluation of port connections.
        Also, discard the evaluation of the functions for all
        the n possibilities. This means that for n instances
        of a contract A, we exclude all the n from future
        appearance
        '''
        #import pdb
        #pdb.set_trace()
        LOG.debug('elaborate rejection list')
        contract_instances = [model[candidate] for candidate in candidates]
        for c_m in contract_instances:
            c_m.__hash__ = types.MethodType(zcontract_hash, c_m)


        size = len(candidates)
        c_set = set([self.contract_model_instances[c_model] for c_model in contract_instances])

        c_list = [self.contract_model_instances[c_model] for c_model in contract_instances]
        #create inverse dict: contract to index
        c_pos = {c_list[ind]: ind for ind in range(0, size) }

        #create inverse model dict: contract to candidate model
        c_mod = {self.contract_model_instances[c_model]: c_model
                 for c_model in contract_instances}

        all_cand = {c_a:
                {simplify(self.ZContract.id(m_a)).as_long(): m_a
                 for m_a in self.contract_model_instances
                 if self.contract_model_instances[m_a] == c_a}
                for c_a in c_set}

        spec_c = self.property_contract
        spec_m = self.property_model
        #ports
        ports = self.port_dict

        #funcs
        func = self.connected_ports
        not_f = Not
        and_f = And

        constraints = [not_f(and_f([func(all_cand[c_a][order[c_pos[c_a]]],
                                                           all_cand[c_b][order[c_pos[c_b]]],
                                                           ports[name_a],
                                                           ports[name_b]) ==
                                      model.eval(func(c_mod[c_a],
                                                                      c_mod[c_b],
                                                                      ports[name_a],
                                                                      ports[name_b]),
                                                 model_completion=True)
                                      for c_a in all_cand
                                      #if (z3.simplify(self.ZContract.id(c_mod[c_a])).as_long() ==
                                      #   order[c_pos[c_a]])
                                      for c_b in all_cand
                                      #if (z3.simplify(self.ZContract.id(c_mod[c_b])).as_long() ==
                                      #   order[c_pos[c_b]])
                                      for name_a in c_a.ports_dict
                                      for name_b in c_b.ports_dict
                                      #if name_a in c_a.ports_dict
                                      #if name_b in c_b.ports_dict
                                      ] +
                                      [func(spec_m,
                                                            all_cand[c_c][order[c_pos[c_c]]],
                                                            ports[name_p],
                                                            ports[name_c]) ==
                                       model.eval(func(spec_m,
                                                                       c_mod[c_c],
                                                                       ports[name_p],
                                                                       ports[name_c]),
                                                  model_completion=True)
                                      for c_c in all_cand
                                      #if (z3.simplify(self.ZContract.id(c_mod[c_c])).as_long() ==
                                      #   order[c_pos[c_c]])
                                      for name_p in spec_c.ports_dict
                                      for name_c in c_c.ports_dict
                                      ]
                                    )
                            )
                        for order in itertools.product(range(size), repeat=size)
                      ]

        #apply the same set of rules for candidates of the same type

        #LOG.debug('log rejection constraints')
        #LOG.debug(constraints)
        LOG.debug('add rejected models constraints')
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




    def build_composition_from_model(self, model, spec, candidates, complete_model=False):
        '''
        builds a contract composition out of a model
        '''

        contracts = {}
        spec_contract = spec.copy()

        #LOG.debug(spec_contract)

        #instantiate single contracts
        for candidate in candidates:
            c_m = model[candidate]
            c_m.__hash__ = types.MethodType(zcontract_hash, c_m)
            c_name = str(simplify(self.ZContract.base_name(c_m)))
            id_c = str(simplify(self.ZContract.id(c_m)))
            #LOG.debug(c_name, id_c)
            contract = type(self.contract_model_instances[c_m])(c_name+id_c)

            #LOG.debug(contract)
            #LOG.debug(c_m)
            contracts[c_m] = contract

        extended_contracts = dict(contracts.items() + [(self.property_model, spec_contract)])

        #start composition
        c_set = set(contracts.viewvalues())
        #c_set.add(contracts.values()[0])
        mapping = CompositionMapping(c_set)

        #start with connections for the spec
        for m_b in contracts:
            c_b = extended_contracts[m_b]

            for ((p_a_name, p_a), (p_b_name, p_b)) in itertools.product(spec_contract.ports_dict.items(), c_b.ports_dict.items()):
                if p_a != p_b:
                    pm_a = getattr(self.PortBaseName, p_a_name)
                    pm_b = getattr(self.PortBaseName, p_b_name)
                    if is_true(model.eval(self.connected_ports(self.property_model, m_b, pm_a, pm_b),
                                       model_completion=True)):
                        #LOG.debug(c_a)
                        #LOG.debug(p_a_name)
                        #LOG.debug(p_a.unique_name)
                        #LOG.debug('--')
                        #LOG.debug(c_b)
                        #LOG.debug(p_b_name)
                        #LOG.debug(p_b.unique_name)
                        #LOG.debug('**')
                        #c_a.connect_to_port(p_a, p_b)
                        #connect directly
                        spec_contract.connect_to_port(p_a, p_b)

        #connections among candidates
        for m_a, m_b in itertools.combinations_with_replacement(contracts, 2):
            c_a = contracts[m_a]
            c_b = contracts[m_b]
            for ((p_a_name, p_a), (p_b_name, p_b)) in itertools.product(c_a.ports_dict.items(), c_b.ports_dict.items()):
                if p_a != p_b:
                    pm_a = getattr(self.PortBaseName, p_a_name)
                    pm_b = getattr(self.PortBaseName, p_b_name)
                    if is_true(model.eval(self.connected_ports(m_a, m_b, pm_a, pm_b),
                                       model_completion=True)):
                        #LOG.debug(c_a)
                        #LOG.debug(p_a_name)
                        #LOG.debug(p_a.unique_name)
                        #LOG.debug('--')
                        #LOG.debug(c_b)
                        #LOG.debug(p_b_name)
                        #LOG.debug(p_b.unique_name)
                        #LOG.debug('**')
                        #c_a.connect_to_port(p_a, p_b)
                        mapping.connect(p_a, p_b, '%s_%s' % (c_a.unique_name, p_a.base_name))
                        assert(not (p_a.is_output and p_b.is_output))
                    else:
                        mapping.add(p_a, '%s_%s' % (c_a.unique_name, p_a.base_name))
                        mapping.add(p_b, '%s_%s' % (c_b.unique_name, p_b.base_name))

        for contract in extended_contracts.values():
            LOG.debug(contract)

        if not complete_model:
            c_set = self.filter_candidate_contracts_for_composition(c_set, spec_contract)

        #compose
        root = c_set.pop()
        
        #c_set.add(root.copy())
        
        composition = root.compose(c_set, composition_mapping=mapping)

        LOG.debug(composition)
        LOG.debug(spec_contract)
        
        return composition, spec_contract, contracts


SMTModelFactory.register(Z3Interface)


class NotSynthesizableError(Exception):
    '''
    raised if it is not possible to synthesize a controller
    '''
    pass

#instance a public interface
#Z3 = Z3Interface()

