'''
This module includes the interface classes and functions for the Z3 SMT solver

Author: Antonio Iannopollo
'''

import logging
from pycox.smt_factory import SMTModelFactory
import z3
import itertools

LOG = logging.getLogger()
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

        self.library = library

        self.property_model = None
        #self.ComponentBaseName = None

        self.contracts_dict = {}
        #self.portc_types = {}
        #self.mapping_datatypes = {}
        #self.mapping_pairs = {}
        self.contract_model_instances = {}
        self.port_names = []

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

        self.solver = None

    @property
    def extended_instances(self):
        '''
        returns library instances plus property model 
        '''
        assert self.property_model is not None

        return dict(self.contract_model_instances.items() + (self.property_model, self.property_contract))

    def initiliaze_solver(self, property_contract):
        '''
        Create environment and models from library
        '''
        port_name_pairs = self.library.get_port_names_pairs
        contract_name_pairs = self.library.get_contract_name_pairs
        component_name_pairs = self.library.get_component_name_pairs

        #extend port names with property ones
        _ = [port_name_pairs.append(port.base_name, port.unique_name)
             for port in property_contract.ports_dict]

        #extends contract names
        contract_name_pairs.append(property_contract.base_name, property_contract.unique_name)

        self.property_model = self.create_contract_model(property_contract, is_library_elem=False)
        self.property_contract = property_contract

        self.create_z3_environment(port_name_pairs, contract_name_pairs, component_name_pairs)


    def initialize_for_fixed_size(self, size):
        '''
        Instantiate structures for a given size
        '''

        for _ in range(0, size):
            for component in self.library.components:
                self.create_component_model(component)

        #initialize the solver functions
        self.define_initial_constraints()
        self.define_initial_connections()

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

    def create_contract_model(self, contract, is_library_elem=True):
        '''
        override from SMTModelFactory method
        '''
        #create port_list
        input_list = self.ZPortList.bottom
        output_list = self.ZPortList.bottom

        for port in contract.input_ports_dict.values():
            z_port = self.create_port_model(port, is_library_elem)
            input_list = self.ZPortList.node(z_port, input_list)

        for port in contract.output_ports_dict.values():
            z_port = self.create_port_model(port, is_library_elem)
            output_list = self.ZPortList.node(z_port, output_list)


        #declare ammissible names for each contract
        #it's ok to store this data now
        self.contracts_dict[contract.unique_name] = contract

        #dtype = z3.Datatype(contract.unique_name)
        #_ = [dtype.declare(port_base_name) for port_base_name in contract.ports_dict]
        #self.portc_types[contract] = dtype.create()


        model = self.ZContract.contract(getattr(self.ContractBaseName,
                                                contract.base_name),
                                        getattr(self.ContractUniqueName,
                                                contract.unique_name),
                                        len(contract.input_ports_dict),
                                        input_list,
                                        len(contract.otput_ports_dict),
                                        output_list, 0)
        if is_library_elem:
            self.contract_model_instances[model] = contract

        return model

    def create_component_model(self, component, is_library_elem=True):
        '''
        override from SMTModelFactory method
        '''
        #create contract list
        #c_list = self.ZContractList.bottom

        return self.create_contract_model(component.contract, is_library_elem)

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
        self.port_names = p_base_names

        self.PortBaseName = z3.Datatype('PortBaseName')
        _ = [self.PortBaseName.declare(x) for x in  set(p_base_names)]
        self.PortBaseName = self.PortBaseName.create()

        #self.PortUniqueName = z3.Datatype('PortUniqueName')
        #_ = [self.PortUniqueName.declare(x) for x in set(p_unique_names)]
        #self.PortUniqueName = self.PortUniqueName.create()


        self.ZPort = z3.Datatype('ZPort')
        self.ZPort.declare('port',
                     ('base_name', self.PortBaseName))
        #             ('unique_name', self.PortUniqueName))

        self.ZPort = self.ZPort.create()

        #build list according to the Tree example
        self.ZPortList = z3.Datatype('ZPortList')
        self.ZPortList.declare('node', ('elem', self.ZPort), ('tail', self.ZPortList))
        self.ZPortList.declare('bottom')

        self.ZPortList = self.ZPortList.create()

        self.ZContract = z3.Datatype('ZContract')
        self.ZContract.declare('contract',
                               ('base_name', self.ContractBaseName),
                               #('unique_name', self.ContractUniqueName),
                               ('num_input', z3.IntSort()),
                               ('input_ports', self.ZPortList),
                               ('num_output', z3.IntSort()),
                               ('output_ports', self.ZPortList),
                               ('hierarchy', z3.IntSort()))

        self.ZContract = self.ZContract.create()

        #self.ZContractList = z3.Datatype('ZContractList')
        #self.ZContractList.declare('node', ('elem', self.ZContract), ('tail', self.ZContractList))
        #self.ZContractList.declare('bottom')

        #self.ZComponent = z3.Datatype('ZComponent')
        #self.ZComponent.declare('component',
        #                        ('base_name', self.ComponentBaseName),
        #                        ('unique_name', self.ComponentUniqueName),
        #                        ('contracts', self.ZContractList))



        self.solver = z3.Solver()


    def define_initial_constraints(self):
        '''
        populate smt functions easily identifiable as total
        '''
        constraints = []

        #define functions from scratch.
        #Since we are adding components for each n, we need to re-declare all the
        #function values. We could try to incrementally add constraints,
        #without recreating everything each time...
        self.contract_has_port_wbase_name = z3.Function('contract_has_port_wbase_name',
                                                        self.ZContract,
                                                        self.PortBaseName,
                                                        z3.BoolSort())

        self.port_is_input = z3.Function('port_is_input',
                                          self.PortBaseName,
                                          self.ZContract,
                                          z3.BoolSort())
        self.port_is_output = z3.Function('port_is_input',
                                          self.PortBaseName,
                                          self.ZContract,
                                          z3.BoolSort())

        self.connected = z3.Function('connected',
                                     self.ZContract,
                                     self.ZContract,
                                     z3.BoolSort())

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


        for (model, contract) in self.extended_instances.items():
            for port_name in self.port_names:
                if port_name in contract.input_ports_dict:
                    constraints.append(self.contract_has_port_wbase_name(model, port_name) == True)
                    constraints.append(self.port_is_input(port_name, model) == True)
                    constraints.append(self.port_is_output(port_name, model) == False)
                elif port_name in contract.output_ports_dict:
                    constraints.append(self.contract_has_port_wbase_name(model, port_name) == True)
                    constraints.append(self.port_is_input(port_name, model) == False)
                    constraints.append(self.port_is_output(port_name, model) == True)
                else:
                    constraints.append(self.contract_has_port_wbase_name(model, port_name) == False)
                    constraints.append(self.port_is_input(port_name, model) == False)
                    constraints.append(self.port_is_output(port_name, model) == False)

        return constraints

    def define_initial_connections(self):
        '''
        Two outputs cannot be connected. Ports not related to contracts, cannot be connected
        Connections are transytive and symmetric
        '''
        constraints = []
        for (m_a, m_b) in itertools.combinations(self.extended_instances.keys(), 2):
            c_a = self.contract_model_instances[m_a]
            c_b = self.contract_model_instances[m_b]

            #sub_constr_and = []
            sub_constr = []
            conn_out_constr = []

            for (p_a, p_b) in itertools.product(self.port_names, 2):
                #if a is connected to b, then b is connected to a and vice versa
                constraints.append(self.connected_ports(m_a, m_b, p_a, p_b) ==
                                   self.connected_ports(m_b, m_a, p_b, p_a))

                #sub_constr_and.append(self.connected_ports(m_a, m_b, p_a, p_b) == False)
                sub_constr.append(self.connected_ports(m_a, m_b, p_a, p_b) == True)

                conn_out_constr.append(z3.And(self.connected_ports(m_a, m_b, p_a, p_b) == True,
                                           self.port_is_output(p_a, m_a),
                                           self.port_is_output(p_b, m_b)))

                if (p_a not in c_a.ports_dict) or (p_b not in c_b):
                    constraints.append(self.connected_ports(m_a, m_b, p_a, p_b) == False)

                elif ((m_a in self.contract_model_instances) and (m_b in self.contract_model_instances)
                       and (p_a in c_a.output_ports_dict) and (p_b in c_b.output_ports_dict)):
                    #no connections between outputs of library elements
                    constraints.append(self.connected_ports(m_a, m_b, p_a, p_b) == False)

            #connected if there is at least a connection
            constraints.append(z3.Implies(z3.Not(z3.Or(sub_constr)), self.connected(m_a, m_b) == False))
            constraints.append(z3.Implies(z3.Or(sub_constr), self.connected(m_a, m_b) == True))
            constraints.append(self.connected(m_a, m_b) == self.connected(m_b, m_a))

            #output_connection
            constraints.append(self.connected_output(m_a, m_b) == self.connected_output(m_b, m_a))
            constraints.append(z3.Implies(z3.Not(z3.Or(conn_out_constr)),
                                          self.connected_output(m_a, m_b) == False))
            constraints.append(z3.Implies(z3.Or(conn_out_constr),
                                          self.connected_output(m_a, m_b) == True))


        #transitivity of connections
        #HEAVY
        for (m_a, m_b, m_c) in itertools.permutations(self.extended_instances.keys(), 3):
            for (p_a, p_b, p_c) in itertools.product(self.port_names, 3):

                constraints.append(z3.Implies(z3.And(self.connected_ports(m_a, m_b, p_a, p_b) == True,
                                                     self.connected_ports(m_b, m_c, p_b, p_c) == True),
                                              self.connected_ports(m_a, m_c, p_a, p_c == True)))
        return constraints






    def synthetize(self, property_contract):
        '''
        perform synthesis process
        '''
        self.initiliaze_solver(property_contract)

        max_components = len(property_contract.output_ports_dict)

        for size_n in range(1, max_components):
            try:
                res = self.synthesize_fixed_size(property_contract, size_n)
            except NotSynthesizableError:
                LOG.debug("size %d synthesis failed")
            else:
                return res

        raise NotSynthesizableError


    def synthesize_fixed_size(self, property_contract, size):
        '''
        synthesis for a fixed size
        includes constraints:
        we expect 'size' components and (size-1)! mappings.
        1) We need to generate a candidate
        2) We need to verify refinement

        '''
        self.initialize_for_fixed_size(size)

        while True:
            try:
                candidate = self.propose_candidate(property_contract, size)
            except NotSynthesizableError as err:
                raise err
            else:
                try:
                    self.verify_candidate(candidate, property_contract)
                except NotSynthesizableError as err:
                    LOG.debug("candidate not valid")
                else:
                    return candidate

    def propose_candidate(self, property_contract, size):
        '''
        1) We need to create this variables and assert the possibilities
        2) We also need to create the mapping functions. Do we allow feedback? Not for now.
        3) We need to define the refinement relations, where possible. Low priority
        4) Verify and loop

        '''
        #let's start a new session
        self.solver.push()

        #declare variables
        c_list = [z3.Const('c_%s' % i, self.ZContract) for i in range(0, size)]

        #Every component must be unique (we already duplicated)
        self.solver.add(z3.Distinct(c_list))

        for candidate in c_list:
            #candidates must be within library components
            span = [candidate == component for component in self.contract_model_instances]
            self.solver.add(z3.Or(span))

            #candidates need to be connected to 

 
        #we want all the output ports of the property to be connected
        for port in property_contract.output_port.values():
            pass




    def verify_candidate(self, candidate, property_contract):
        '''
        check if a candidate is valid or not
        '''
        pass



SMTModelFactory.register(Z3Interface)


class NotSynthesizableError(Exception):
    '''
    raised if it is not possible to synthesize a controller
    '''
    pass

#instance a public interface
Z3 = Z3Interface()

