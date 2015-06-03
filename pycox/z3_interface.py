'''
This module includes the interface classes and functions for the Z3 SMT solver

Author: Antonio Iannopollo
'''

import logging
from pycox.smt_factory import SMTModelFactory
import z3
import itertools
import types

LOG = logging.getLogger()
LOG.debug('in z3_interface')


def zcontract_hash(obj):
    '''
    hash for z3 contract objects
    '''
    #LOG.debug('hash')
    #LOG.debug(obj)
    #LOG.debug(z3.simplify(obj.sort().accessor(0,6)(obj)))
    return hash(str(z3.simplify(obj.sort().accessor(0,0)(obj))) +
                str(z3.simplify(obj.sort().accessor(0,1)(obj)).as_long()) +
                str(z3.simplify(obj.sort().accessor(0,2)(obj)).as_long()))
    #return obj.hash()

def zcontract_eq(obj, other):
    '''
    equality
    '''
    try:
        return (str(z3.simplify(obj.sort().accessor(0,0)(obj))) ==
                str(z3.simplify(other.sort().accessor(0,0)(other))) and
                z3.simplify(obj.sort().accessor(0,1)(obj)).as_long() ==
                z3.simplify(other.sort().accessor(0,1)(other)).as_long() and
                z3.simplify(obj.sort().accessor(0,2)(obj)).as_long() ==
                z3.simplify(other.sort().accessor(0,2)(other)).as_long())
    except:
        return False

class Z3Interface(object):
    '''
    Interface class for the Z3 SMT solver.
    Extends the class SMTModelFactory
    '''

    def __init__(self, library):
        '''
        init
        '''
        z3.set_param(proof=True)
        self.library = library

        self.property_model = None
        #self.ComponentBaseName = None

        self.contracts_dict = {}
        #self.portc_types = {}
        #self.mapping_datatypes = {}
        #self.mapping_pairs = {}
        self.contract_model_instances = {}
        self.port_names = set()

        #self.ComponentUniqueName = None
        self.PortBaseName = None
        self.PortUniqueName = None
        self.ContractBaseName = None
        self.ContractUniqueName = None

        self.ZPort = None
        self.ZPortList = None
        self.ZContract = None
        self.ZContractList = None
        #self.ZComponent = None

        #self.component_has_contract_wbase_name = None
        self.contract_has_port_wbase_name = None
        self.contract_list_has_contract = None
        self.port_list_has_port = None
        self.port_list_has_port_with_base_name = None
        self.port_list_has_port_with_unique_name = None

        #TODO remember to include mapping
        self.component_refinement = None

        self.counter = itertools.count()
        self.port_dict = {}
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

        self.create_z3_environment(port_name_pairs, contract_name_pairs, component_name_pairs)

        self.property_model = self.create_contract_model(property_contract, 0, is_library_elem=False)
        self.property_contract = property_contract



    def initialize_for_fixed_size(self, size):
        '''
        Instantiate structures for a given size
        '''
        constraints = []

        try:
            self.solver.pop()
        except z3.Z3Exception as err:
            #LOG.debug(err)
            pass

        self.contract_model_instances={}
        for index in range(0, size):
            for component in self.library.components:
                self.create_component_model(component, index)

        #initialize the solver functions
        #constraints += self.define_initial_constraints()
        constraints += self.quantified_initial_contraints()
        constraints += self.define_initial_connections()
        #constraints += self.quantify_initial_connections()

        self.solver.push()
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
                                        z3.BitVecVal(0,2),
                                        z3.BitVecVal(index, 8))


        #add hash
        model.__hash__ = types.MethodType(zcontract_hash, model)
        #add eq
        #model.__eq__ = types.MethodType(zcontract_eq, model)
        if is_library_elem:
            self.contract_model_instances[model] = contract

        return model

    def create_component_model(self, component, index, is_library_elem=True):
        '''
        override from SMTModelFactory method
        '''
        #create contract list
        #c_list = self.ZContractList.bottom

        return self.create_contract_model(component.contract, index, is_library_elem)

    def create_z3_environment(self, ports, contracts, portc_names):
        '''
        Creates basic types for the current library instance
        '''

        #contract names 
        (c_base_names, c_unique_names) = zip(*contracts)

        self.ContractBaseName = z3.Datatype('ContractBaseName')
        _ = [self.ContractBaseName.declare(x) for x in set(c_base_names)]
        self.ContractBaseName = self.ContractBaseName.create()

        self.ContractUniqueName = z3.Datatype('ContractUniqueName')
        _ = [self.ContractUniqueName.declare(x) for x in set(c_unique_names)]
        self.ContractUniqueName = self.ContractUniqueName.create()

        #port names
        (p_base_names, p_unique_names) = zip(*ports)
        self.port_names = set(p_base_names)

        self.PortBaseName = z3.Datatype('PortBaseName')
        _ = [self.PortBaseName.declare(x) for x in  set(p_base_names)]
        self.PortBaseName = self.PortBaseName.create()

        self.port_dict = {name: getattr(self.PortBaseName, name) for name in self.port_names}

        #self.PortUniqueName = z3.Datatype('PortUniqueName')
        #_ = [self.PortUniqueName.declare(x) for x in set(p_unique_names)]
        #self.PortUniqueName = self.PortUniqueName.create()


        self.ZPort = z3.Datatype('ZPort')
        self.ZPort.declare('port',
                     ('base_name', self.PortBaseName))
        #             ('unique_name', self.PortUniqueName))

        self.ZPort = self.ZPort.create()

        #build list according to the Tree example
        #self.ZPortList = z3.Datatype('ZPortList')
        #self.ZPortList.declare('node', ('elem', self.ZPort), ('tail', self.ZPortList))
        #self.ZPortList.declare('bottom')

        #self.ZPortList = self.ZPortList.create()

        self.ZContract = z3.Datatype('ZContract')
        #self.ZContract.declare('contract',
        #                       ('base_name', self.ContractBaseName),
        #                       #('unique_name', self.ContractUniqueName),
        #                       ('num_input', z3.IntSort()),
        #                       ('input_ports', self.ZPortList),
        #                       ('num_output', z3.IntSort()),
        #                       ('output_ports', self.ZPortList),
        #                       ('hierarchy', z3.IntSort()),
        #                       ('id', z3.IntSort()))

        #self.ZContract.declare('contract',
        #                       ('base_name', self.ContractBaseName),
        #                       ('hierarchy', z3.IntSort()),
        #                       ('id', z3.IntSort()))
        self.ZContract.declare('contract',
                               ('base_name', self.ContractBaseName),
                               ('hierarchy', z3.BitVecSort(2)),
                               ('id', z3.BitVecSort(8)))

        self.ZContract = self.ZContract.create()

        #self.ZContractList = z3.Datatype('ZContractList')
        #self.ZContractList.declare('node', ('elem', self.ZContract), ('tail', self.ZContractList))
        #self.ZContractList.declare('bottom')

        #self.ZComponent = z3.Datatype('ZComponent')
        #self.ZComponent.declare('component',
        #                        ('base_name', self.ComponentBaseName),
        #                        ('unique_name', self.ComponentUniqueName),
        #                        ('contracts', self.ZContractList))


        self.contract_has_port_wbase_name = z3.Function('contract_has_port_wbase_name',
                                                        self.ZContract,
                                                        self.PortBaseName,
                                                        z3.BoolSort())

        self.port_is_input = z3.Function('port_is_input',
                                          self.PortBaseName,
                                          self.ZContract,
                                          z3.BoolSort())
        self.port_is_output = z3.Function('port_is_output',
                                          self.PortBaseName,
                                          self.ZContract,
                                          z3.BoolSort())

        self.connected = z3.Function('connected',
                                     self.ZContract,
                                     self.ZContract,
                                     z3.BoolSort())

        #true if two contracts share a connection over output ports
        self.connected_output = z3.Function('connected_output',
                                            self.ZContract,
                                            self.ZContract,
                                            z3.BoolSort())
        self.connected_ports = z3.Function('connected_ports',
                                     self.ZContract,
                                     self.ZContract,
                                     self.PortBaseName,
                                     self.PortBaseName,
                                     z3.BoolSort())

        #completely connected ports
        self.fully_connected = z3.Function('fully_connected',
                                            self.ZContract,
                                            z3.BoolSort())
        #completely connected input
        self.full_input = z3.Function('full_input',
                                            self.ZContract,
                                            z3.BoolSort())
        #completely connected output
        self.full_output = z3.Function('full_output',
                                            self.ZContract,
                                            z3.BoolSort())

        #a certain port is connected
        self.port_is_connected = z3.Function('port_is_connected',
                                            self.ZContract,
                                            self.PortBaseName,
                                            z3.BoolSort())

        self.solver = z3.Solver()


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
        for (model, contract) in self.extended_instances.items():
            for port_name in self.port_names:

                port_name_model = getattr(self.PortBaseName, port_name)


                if port_name in contract.input_ports_dict:
                    constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == True)
                    constraints.append(self.port_is_input(port_name_model, model) == True)
                    constraints.append(self.port_is_output(port_name_model, model) == False)
                elif port_name in contract.output_ports_dict:
                    constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == True)
                    constraints.append(self.port_is_input(port_name_model, model) == False)
                    constraints.append(self.port_is_output(port_name_model, model) == True)
                else:
                    constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == False)
                    constraints.append(self.port_is_input(port_name_model, model) == False)
                    constraints.append(self.port_is_output(port_name_model, model) == False)


        c_a, c_b = z3.Consts('c_a c_b', self.ZContract)
        p_a, p_b = z3.Consts('p_a p_b', self.PortBaseName)

        #all the inputs connected -> full_input
        #in_conn_conditions = [z3.Implies(self.port_is_input(p_a, c_a),
        #                                  self.port_is_connected(c_a, p_a)) for p_a in self.port_dict.values()]

        #condition = [z3.If(z3.And(in_conn_conditions),
        #                                   self.full_input(c_a),
        #                                   z3.Not(self.full_input(c_a))))

        condition = [z3.If(z3.And([z3.Implies(self.port_is_input(p_a, c_a),
                                          self.port_is_connected(c_a, p_a))
                                   for p_a in self.port_dict.values()]),
                                   self.full_input(c_a),
                                   z3.Not(self.full_input(c_a)))
                    for c_a in self.extended_instances]

        constraints += condition


        c_a, c_b = z3.Consts('c_a c_b', self.ZContract)
        p_a, p_b = z3.Consts('p_a p_b', self.PortBaseName)
        #all outputs connectedf -> full_output
        #out_conn_conditions = z3.ForAll([p_a], z3.Implies(self.port_is_output(p_a, c_a),
        #                                              self.port_is_connected(c_a, p_a)))
        #condition = z3.ForAll([c_a], z3.If(out_conn_conditions,
        #                                   self.full_output(c_a),
        #                                   z3.Not(self.full_output(c_a))))
        #constraints.append(condition)
        condition = [z3.If(z3.And([z3.Implies(self.port_is_output(port, contract),
                                              self.port_is_connected(contract, port))
                                   for port in self.port_dict.values()]),
                           self.full_output(contract),
                           z3.Not(self.full_output(contract)))
                     for contract in self.extended_instances]

        constraints += condition

        #all inputs and all outputs -> fully connected
        #condition = z3.ForAll([c_a], z3.If(z3.And(self.full_input(c_a),
        #                                          self.full_output(c_a)),
        #                                   self.fully_connected(c_a),
        #                                   z3.Not(self.fully_connected(c_a))))
        #constraints.append(condition)

        condition = [z3.If(z3.And(self.full_input(contract),
                                  self.full_output(contract)),
                           self.fully_connected(contract),
                           z3.Not(self.fully_connected(contract)))
                     for contract in self.extended_instances]

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

        condition = [z3.If(z3.And(self.contract_has_port_wbase_name(contract, port),
                                   z3.Or([z3.And(self.connected_ports(contract, contract1,
                                                                      port, port1),
                                                 z3.Or(z3.Not(contract == contract1),
                                                       z3.Not(port == port1)))
                                          for port1 in self.port_dict.values()
                                          for contract1 in self.extended_instances]
                                        )
                                   ),
                            self.port_is_connected(contract, port),
                            z3.Not(self.port_is_connected(contract, port)))
                     for port in self.port_dict.values() for contract in self.extended_instances]
        
        constraints += condition

        c_c = z3.Const('c_c', self.ZContract)
        p_c = z3.Const('p_c', self.PortBaseName)

        #connected_ports is symmetric
        #condition = z3.ForAll([c_a, c_b, p_a, p_b],
        #                      (self.connected_ports(c_a, c_b, p_a, p_b) ==
        #                       self.connected_ports(c_b, c_a, p_b, p_a)))
        #constraints.append(condition)


        #connected_ports is also transitive
        condition = z3.ForAll([c_a, c_b, c_c, p_a, p_b, p_c],
                              z3.Implies(z3.And(self.connected_ports(c_a, c_b, p_a, p_b),
                                                self.connected_ports(c_b, c_c, p_b, p_c)),
                                         self.connected_ports(c_a, c_c, p_a, p_c)
                                        )
                             )
        constraints.append(condition)


        # A LOT SLOWER  
        #condition = [z3.Implies(z3.And(self.connected_ports(c_a, c_b, p_a, p_b),
        #                               self.connected_ports(c_b, c_c, p_b, p_c)),
        #                        self.connected_ports(c_a, c_c, p_a, p_c)
        #                       )
        #             for p_a in self.port_dict.values() for p_b in self.port_dict.values()
        #             for p_c in self.port_dict.values() for c_a in self.extended_instances
        #             for c_b in self.extended_instances for c_c in self.extended_instances]

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

#    def define_initial_constraints(self):
#        '''
#        populate smt functions easily identifiable as total
#        '''
#        constraints = []
#
#        #define functions from scratch.
#        #Since we are adding components for each n, we need to re-declare all the
#        #function values. We could try to incrementally add constraints,
#        #without recreating everything each time...
# 
#        #define structural properties:
#        #ports
#        #LOG.debug(self.extended_instances.items())
#        for (model, contract) in self.extended_instances.items():
#            in_conn_conditions = []
#            out_conn_conditions = []
#            for port_name in self.port_names:
#
#                port_name_model = getattr(self.PortBaseName, port_name)
#
#                port_connected_conditions = []
#
#                if port_name in contract.input_ports_dict:
#                    constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == True)
#                    constraints.append(self.port_is_input(port_name_model, model) == True)
#                    constraints.append(self.port_is_output(port_name_model, model) == False)
#                elif port_name in contract.output_ports_dict:
#                    constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == True)
#                    constraints.append(self.port_is_input(port_name_model, model) == False)
#                    constraints.append(self.port_is_output(port_name_model, model) == True)
#                else:
#                    constraints.append(self.contract_has_port_wbase_name(model, port_name_model) == False)
#                    constraints.append(self.port_is_input(port_name_model, model) == False)
#                    constraints.append(self.port_is_output(port_name_model, model) == False)
#
#                #define rules for in connections
#                in_conn_conditions.append(z3.Implies(self.port_is_input(port_name_model, model),
#                                          self.port_is_connected(model, port_name_model)))
#
#                out_conn_conditions.append(z3.Implies(self.port_is_output(port_name_model, model),
#                                          self.port_is_connected(model, port_name_model)))
#
#                #a port is connected if there is at least a valid connection
#                for other_model in self.extended_instances:
#                    for other_port_name in self.port_names:
#                        other_port_name_model = getattr(self.PortBaseName, other_port_name)
#                        port_connected_conditions.append(self.connected_ports(model,
#                                                                              other_model,
#                                                                              port_name_model,
#                                                                              other_port_name_model))
#                condition = z3.And(self.contract_has_port_wbase_name(model, port_name_model),
#                                   z3.Or(port_connected_conditions))
#                constraints.append(z3.If(condition,
#                                         self.port_is_connected(model, port_name_model),
#                                         z3.Not(self.port_is_connected(model, port_name_model))))
#
#            #if for all the inputs, the port is connected, the the model is fully input connected
#            condition = z3.And(in_conn_conditions)
#            condition = z3.If(condition, self.full_input(model), z3.Not(self.full_input(model)))
#            constraints.append(condition)
#
#            #if for all the outputs, the port is connected, the the model is fully output connected
#            condition = z3.And(out_conn_conditions)
#            condition = z3.If(condition, self.full_output(model), z3.Not(self.full_output(model)))
#            constraints.append(condition)
#
#            #if full_input and full_output, then model is fully connected, else it is not
#            constraints.append(z3.If(z3.And(self.full_input(model),
#                                            self.full_output(model)),
#                                     self.fully_connected(model),
#                                     z3.Not(self.fully_connected(model))))
#
#
#
#        return constraints

#    def quantify_initial_connections(self):
#        '''
#        quantified version of 'define initial connections'
#        '''
#        constraints = []
#
#        c_a, c_b, c_c = z3.Consts('c_a c_b c_c', self.ZContract)
#        p_a, p_b, p_c = z3.Consts('p_a p_b p_c', self.PortBaseName)
#
#        #connected_ports is reflexive
#        condition = z3.ForAll([c_a, c_b, p_a, p_b],
#                              (self.connected_ports(c_a, c_b, p_a, p_b) ==
#                               self.connected_ports(c_b, c_a, p_b, p_a)))
#        constraints.append(condition)
#
#        #invalid ports cannot be connected
#        condition = z3.ForAll([c_a, c_b, p_a, p_b],
#                              z3.Implies(z3.Or(z3.Not(self.contract_has_port_wbase_name(c_a, p_a)),
#                                               z3.Not(self.contract_has_port_wbase_name(c_b, p_b))),
#                                         self.connected_ports(c_a, c_b, p_a, p_b)==False)
#                              )
#        constraints.append(condition)
#
#        #for all but spec, outputs cannot be connected
#        condition = z3.ForAll([c_a, c_b, p_a, p_b],
#                              z3.Implies(z3.And(c_a != self.property_model,
#                                                c_b != self.property_model,
#                                                self.port_is_output(p_a, c_a),
#                                                self.port_is_output(p_b, c_b)),
#                                         self.connected_ports(c_a, c_b, p_a, p_b)==False)
#                              )
#        #constraints.append(condition)
#
#        #two contracts connected if there is at least a common connection
#        #symmetric->inferred by connected_ports
#        condition = z3.ForAll([c_a, c_b],
#                              z3.If(z3.Exists([p_a, p_b],
#                                              self.connected_ports(c_a, c_b, p_a, p_b)),
#                                    self.connected(c_a, c_b) == True,
#                                    self.connected(c_a, c_b) == False
#                                    )
#                              )
#        constraints.append(condition)
#
#        #connected on output(only for specification model)
#        condition = z3.ForAll([c_a, c_b],
#                              z3.If(z3.Exists([p_a, p_b],
#                                              z3.And(self.connected_ports(c_a, c_b, p_a, p_b),
#                                                     self.port_is_output(p_a, c_a),
#                                                     self.port_is_output(p_b, c_b)
#                                                     )
#                                              ),
#                                    self.connected_output(c_a, c_b) == True,
#                                    self.connected_output(c_a, c_b) == False,
#                                    )
#                              )
#        constraints.append(condition)
#
#        #connected
#        condition = z3.ForAll([c_a, c_b],
#                              z3.If(z3.Exists([p_a, p_b],
#                                              self.connected_ports(c_a, c_b, p_a, p_b),
#                                              ),
#                                    self.connected(c_a, c_b) == True,
#                                    self.connected(c_a, c_b) == False,
#                                    )
#                              )
#        constraints.append(condition)
#
#        #connected_ports is also transitive
#        condition = z3.ForAll([c_a, c_b, c_c, p_a, p_b, p_c],
#                              z3.Implies(z3.And(self.connected_ports(c_a, c_b, p_a, p_b),
#                                                self.connected_ports(c_b, c_c, p_b, p_c)),
#                                         self.connected_ports(c_a, c_c, p_a, p_c)
#                                        )
#                             )
#        constraints.append(condition)
#
#
#        return constraints




    def define_initial_connections(self):
        '''
        Two outputs cannot be connected. Ports not related to contracts, cannot be connected
        Connections are transitive and symmetric
        '''
        constraints = []

        #loop over all the possible instances
        #NOT considering the spec   
        #for (m_a, m_b) in itertools.permutations(self.extended_instances.keys(), 2):
        for (m_a, m_b) in itertools.product(self.extended_instances.keys(), repeat=2):
            #c_a = self.contract_model_instances[m_a]
            #c_b = self.contract_model_instances[m_b]
            c_a = self.extended_instances[m_a]
            c_b = self.extended_instances[m_b]

            #sub_constr_and = []
            sub_constr = []
            conn_out_constr = []
            diff_model = []

            #LOG.debug('iteration')
            for item in itertools.product(self.port_names, repeat=2):
            #for item in itertools.combinations_with_replacement(set(self.port_names), 2):

                #LOG.debug(item)
                (p_a, p_b) = item
                p_a_model = getattr(self.PortBaseName, p_a)
                p_b_model = getattr(self.PortBaseName, p_b)

                #if a is connected to b, then b is connected to a and vice versa
                #symmetric
                constraints.append(self.connected_ports(m_a, m_b, p_a_model, p_b_model) ==
                                   self.connected_ports(m_b, m_a, p_b_model, p_a_model))

                #used in implication, later, but only if not the same component and port
                sub_constr.append(self.connected_ports(m_a, m_b, p_a_model, p_b_model))
                conn_out_constr.append(z3.And(self.connected_ports(m_a, m_b,
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
                    constraints.append(z3.Not(self.connected_ports(m_a, m_b, p_a_model, p_b_model)))
                #connected_port is reflexive - but never in the case without replacement, or product
                elif (z3.is_true(z3.simplify(m_a == m_b)) and
                     z3.is_true(z3.simplify(p_a_model == p_b_model))):
                    #LOG.debug('2')
                    constraints.append(self.connected_ports(m_a, m_b, p_a_model, p_b_model))

                elif (z3.is_false(z3.simplify(m_a == self.property_model)) and
                        z3.is_false(z3.simplify(m_b == self.property_model))
                       and (p_a in c_a.output_ports_dict) and (p_b in c_b.output_ports_dict)):
                #elif (p_a in c_a.output_ports_dict) and (p_b in c_b.output_ports_dict):
                    #no connections between outputs of library elements
                    #LOG.debug('no output-----------')
                    #LOG.debug(m_a)
                    #LOG.debug(m_b)
                    #LOG.debug(p_a)
                    #LOG.debug(p_b)
                    constraints.append(z3.Not(self.connected_ports(m_a, m_b, p_a_model, p_b_model)))
                    #pass

            #two contracts connected if there is at least a common connection
            #constraints.append(z3.Implies(z3.Not(z3.Or(sub_constr)), self.connected(m_a, m_b) == False))
            #constraints.append(z3.Implies(z3.Or(sub_constr), self.connected(m_a, m_b) == True))
            constraints.append(z3.If(z3.Or(sub_constr),
                                     self.connected(m_a, m_b)==True,
                                     self.connected(m_a, m_b)==False))
            
            constraints.append(self.connected(m_a, m_b) == self.connected(m_b, m_a))

            #output_connection
            constraints.append(self.connected_output(m_a, m_b) == self.connected_output(m_b, m_a))
            #constraints.append(z3.Implies(z3.Not(z3.Or(conn_out_constr)),
            #                              self.connected_output(m_a, m_b) == False))
            #constraints.append(z3.Implies(z3.Or(conn_out_constr),
            #                              self.connected_output(m_a, m_b) == True))
            constraints.append(z3.If(z3.Or(conn_out_constr),
                                     self.connected_output(m_a, m_b) == True,
                                     self.connected_output(m_a, m_b) == False
                                     )
                              )

        #transitivity of connections
        #HEAVY
        #for (m_a, m_b, m_c) in itertools.permutations(self.extended_instances.keys(), 3):
        #    for item in itertools.product(set(self.port_names), repeat=3):
        #        (p_a, p_bi, p_c) = item
        #        p_a_model = getattr(self.PortBaseName, p_a)
        #        p_b_model = getattr(self.PortBaseName, p_b)
        #        p_c_model = getattr(self.PortBaseName, p_c)
        #        constraints.append(z3.Implies(z3.And(self.connected_ports(m_a, m_b, p_a_model, p_b_model) == True,
        #                                             self.connected_ports(m_b, m_c, p_b_model, p_c_model) == True),
        #                                      self.connected_ports(m_a, m_c, p_a_model, p_c_model) == True))
        
        
        return constraints



    def exclude_candidate_type(self, candidate, discarded_model):
        '''
        make sure that a future solution will not include any contract
        identycal to the one discarded
        '''
        constraints = []

        model_contract = self.extended_instances[discarded_model]
        #constraints.append(candidate != discarded_model)

        for (model, contract) in self.extended_instances.items():
            if contract.base_name == model_contract.base_name:
                constraints.append(candidate != discarded_model)

        return constraints


    def all_models_completely_connected(self, candidate_models):
        '''
        All ports need to be connected
        '''
        constraints = []

        for model in candidate_models:
            constraints.append(self.fully_connected(model))

        return constraints

    def models_disconnected_if_not_solution(self, candidate_models):
        '''
        if not part of solution, everything disconnected
        '''
        constraints = []
        part1 = {}

        #for m_a in self.contract_model_instances:
        #    conditions = []
        #    for candidate in candidate_models:
        #        conditions.append(m_a == candidate)
        #    part1[m_a] = conditions
        #
        ##not considering repetitions e.g. (a,a)
        #for m_a, m_b in itertools.combinations(self.contract_model_instances.keys(), 2):
        #    prop = z3.Implies(z3.Not(z3.And(z3.Or(part1[m_a]),
        #                                    z3.Or(part1[m_b]))),
        #                      self.connected(m_a, m_b)==False)
        #    constraints.append(prop)
        
        for m_a in self.contract_model_instances:
            conditions = []
            for candidate in candidate_models:
                conditions.append(m_a == candidate)
            part1[m_a] = conditions
        
        for (m_a, c_a) in self.contract_model_instances.items():
            part2 = []
            for port_name in c_a.ports_dict:
                p_a = getattr(self.PortBaseName, port_name)
                part2.append(z3.Not(self.port_is_connected(m_a, p_a)))

            prop = z3.Implies(z3.Not(z3.Or(part1[m_a])),
                              z3.And(part2))

            constraints.append(prop)
       

        return constraints


    def property_outputs_not_together(self):
        '''
        Output ports of property can be connected to other outputs, but not
        among themselves
        '''
        constraints = []

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



    def synthetize(self, property_contract):
        '''
        perform synthesis process
        '''
        self.initiliaze_solver(property_contract)

        max_components = len(property_contract.output_ports_dict)

        #property model has to be fully connected - always true
        self.solver.add(self.fully_connected(self.property_model))

        for size_n in range(1, max_components+1):
            try:
                res = self.synthesize_fixed_size(size_n)
            except NotSynthesizableError:
                LOG.debug("size %d synthesis failed")
            else:
                return res

        raise NotSynthesizableError


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
        self.initialize_for_fixed_size(size)

        #declare variables
        c_list = [z3.Const('c_%s' % i, self.ZContract) for i in range(0, size)]

        #Every component must be unique (we already duplicated)
        self.solver.add(z3.Distinct(c_list))

        #All the candidates fully connected
        self.solver.add(self.all_models_completely_connected(c_list))

        #property has to be fully connected
        self.solver.add(self.fully_connected(self.property_model))

        #Spec cannot be connected to itself on outputs
        #self.solver.add(self.connected_output(self.property_model, self.property_model)==False)
        #self.solver.add(self.property_outputs_not_together())

        #models disconnected if not solution
        self.solver.add(self.models_disconnected_if_not_solution(c_list))

        #add full input for models, too

        for candidate in c_list:
            #candidates must be within library components
            span = [candidate == component for component in self.contract_model_instances]
            self.solver.add(z3.Or(span))

            #but candidate cannot be the spec itself
            self.solver.add(z3.Not(candidate==self.property_model))

            #spec needs to be connected to candidates
            self.solver.add(self.connected_output(candidate, self.property_model))

        while True:
            try:
                candidate = self.propose_candidate(size)
            except NotSynthesizableError as err:
                raise err
            else:
                try:
                    self.verify_candidate(candidate, c_list)
                except NotSynthesizableError as err:
                    LOG.debug("candidate not valid")
                else:
                    return candidate

    def propose_candidate(self, size):
        '''
        generate a model
        '''
        z3.set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)
        #LOG.debug(self.solver.assertions)

        LOG.debug('start solving')
        res = self.solver.check()
        LOG.debug(res)
        LOG.debug('done')
        if res == z3.sat:
            LOG.debug(self.solver.model())
        else:
            LOG.debug(self.solver.proof())

        try:
            model = self.solver.model()
        except z3.Z3Exception:
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
        composition = self.build_composition_from_model(model, candidates)


    def build_composition_from_model(self, model, candidates):
        '''
        builds a contract composition out of a model
        '''

        contracts = {}
        spec_contract = self.property_contract.copy()
        LOG.debug(spec_contract)
        #instantiate single contracts
        for candidate in candidates:
            c_m = model[candidate]
            c_m.__hash__ = types.MethodType(zcontract_hash, c_m)
            c_name = str(z3.simplify(self.ZContract.base_name(c_m)))
            id_c = str(z3.simplify(self.ZContract.id(c_m)))
            #LOG.debug(c_name, id_c)
            contract = type(self.contract_model_instances[c_m])(c_name+id_c)
            LOG.debug(contract)
            contracts[c_m] = contract

        extended_contracts = dict(contracts.items() + [(self.property_model, spec_contract)])

        #connections
        for m_a, m_b in itertools.combinations_with_replacement(extended_contracts, 2):
            c_a = extended_contracts[m_a]
            c_b = extended_contracts[m_b]
            for ((p_a_name, p_a), (p_b_name, p_b)) in itertools.product(c_a.ports_dict.items(), c_b.ports_dict.items()):
                if p_a != p_b:
                    pm_a = getattr(self.PortBaseName, p_a_name)
                    pm_b = getattr(self.PortBaseName, p_b_name)
                    if z3.is_true(model.eval(self.connected_ports(m_a, m_b, pm_a, pm_b),
                                       model_completion=True)):
                        #LOG.debug(c_a)
                        #LOG.debug(p_a_name)
                        #LOG.debug(p_a.unique_name)
                        #LOG.debug('--')
                        #LOG.debug(c_b)
                        #LOG.debug(p_b_name)
                        #LOG.debug(p_b.unique_name)
                        #LOG.debug('**')
                        c_a.connect_to_port(p_a, p_b)
                        assert(c_a == spec_contract or
                               c_b == spec_contract or
                               not (p_a.is_output and p_b.is_output))

        for contract in extended_contracts.values():
            LOG.debug(contract)



SMTModelFactory.register(Z3Interface)


class NotSynthesizableError(Exception):
    '''
    raised if it is not possible to synthesize a controller
    '''
    pass

#instance a public interface
#Z3 = Z3Interface()

