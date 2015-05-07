'''
This module includes the interface classes and functions for the Z3 SMT solver

Author: Antonio Iannopollo
'''

import logging
from pycox.smt_factory import SMTModelFactory
import z3

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

        #self.ComponentBaseName = None

        self.contracts_dict = {}
        self.portc_types = {}
        self.mapping_functions = {}
        self.contract_models = {}
        self.port_models = {}

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

    def initiliaze_library(self):
        '''
        Create environment and models from library
        '''

        for component in self.library.components:


    def create_port_model(self, port):
        '''
        override from SMTModelFactory method
        '''

        model = self.ZPort.port(getattr(self.PortBaseName, port.base_name),
                                getattr(self.PortUniqueName, port.unique))


        return model

    def create_contract_model(self, contract):
        '''
        override from SMTModelFactory method
        '''
        #create port_list
        input_list = self.ZPortList.bottom
        output_list = self.ZPortList.bottom

        for port in contract.input_ports_dict.values():
            z_port = self.create_port_model(port)
            input_list = self.ZPortList.node(z_port, input_list)

        for port in contract.output_ports_dict.values():
            z_port = self.create_port_model(port)
            output_list = self.ZPortList.node(z_port, output_list)


        #declare ammissible names for each contract
        #it's ok to store this data now
        self.contracts_dict[contract.unique_name] = contract

        dtype = z3.Datatype(contract.unique_name)
        _ = [dtype.declare(port_base_name) for port_base_name in contract.ports_dict]
        self.portc_types[contract.unique_name] = dtype.create()


        model = self.ZContract.contract(getattr(self.ContractBaseName,
                                                contract.base_name),
                                        getattr(self.ContractUniqueName,
                                                contract.unique_name),
                                        input_list, output_list)


        return model

    def create_component_model(self, component):
        '''
        override from SMTModelFactory method
        '''
        #create contract list
        #c_list = self.ZContractList.bottom

        return self.create_contract_model(component.contract)

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

        self.PortBaseName = z3.Datatype('PortBaseName')
        _ = [self.PortBaseName.declare(x) for x in  set(p_base_names)]
        self.PortBaseName = self.PortBaseName.create()

        self.PortUniqueName = z3.Datatype('PortUniqueName')
        _ = [self.PortUniqueName.declare(x) for x in set(p_unique_names)]
        self.PortUniqueName = self.PortUniqueName.create()


        self.ZPort = z3.Datatype('ZPort')
        _ = [self.ZPort.declare()]
        #self.ZPort.declare('port',
        #             ('base_name', self.PortBaseName),
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
                               ('unique_name', self.ContractUniqueName),
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

#Z3 does not handle recursive declarations with quantifiers:(

# def port_assert_on_list(function, port_assertion, p, l):
#     return ForAll([p, l],
#              If(PortList.is_bottom(l),
#                 function(l, p) == False,
#                 If(port_assertion,
#                    function(l, p) == True,
#                    function(l, p) == function(PortList.port_list(l), p)
#                   )
#                )
#              )

#declare functions
        self.port_list_has_port = z3.Function('port_list_has_port',
                                              self.ZPortList,
                                              self.ZPort,
                                              z3.BoolSort())
        self.contract_list_has_contract = z3.Function('contract_list_has_contract',
                                                      self.ZContractList,
                                                      self.ZContract,
                                                      z3.BoolSort())
        self.port_list_has_port_with_base_name = z3.Function('port_list_has_port_with_base_name',
                                                             self.ZPortList,
                                                             self.PortBaseName,
                                                             z3.BoolSort())
        self.port_list_has_port_with_unique_name = z3.Function('port_list_has_port_with_unique_name',
                                                               self.ZPortList,
                                                               self.PortUniqueName,
                                                               z3.BoolSort())

        self.contract_has_port_wbase_name = z3.Function('contract_has_port_wbase_name',
                                                        self.ZContract,
                                                        self.PortBaseName,
                                                        z3.BoolSort())
        #self.component_has_contract_wbase_name = z3.Function('component_has_contract_wbase_name',
        #                                                     self.ZComponent,
        #                                                     self.ContractBaseName,
        #                                                     z3.BoolSort())
#p = Const('p', Port)
#l = Const('l', PortList)


    def define_has_port_constraints(self, port_list, port):
        iter_list = port_list

        while z3.is_false(z3.simplify(self.ZPortList.is_bottom(iter_list))):
            if z3.is_true(z3.simplify(self.ZPortList.elem(iter_list) == port)):
                return [self.port_list_has_port(port_list, port) == True]

            iter_list = self.ZPortList.tail(iter_list)

        return [self.port_list_has_port(port_list, port) == False]


    def define_port_list_has_port_name(self, port_list, port_base_name):

        iter_list = port_list

        while z3.is_false(z3.simplify(self.ZPortList.is_bottom(iter_list))):
            if z3.is_true(z3.simplify(self.ZPort.base_name(self.ZPortList.elem(iter_list)) == port_base_name)):
                #return [list_has_port_with_base_name(port_list, port_base_name) == True]
                return True

            iter_list = self.ZPortList.tail(iter_list)


        #return [list_has_port_with_base_name(port_list, port_base_name) == False]
        return False


    def define_contract_has_port_wname_constraints(self, contract, port_base_name):
        constraints = []
        input_l = self.ZContract.input_ports(contract)
        output_l = self.ZContract.output_ports(contract)

        if (self.define_port_list_has_port_name(input_l, port_base_name) or
            self.define_port_list_has_port_name(output_l, port_base_name)):
            return [self.contract_has_port_wbase_name(contract, port_base_name) == True]

        return [self.contract_has_port_wbase_name(contract, port_base_name) == False]


    def define_contract_has_port_wname_total(self, contract_list):
        constraints = []

        for contract in contract_list:
            for port_base_name in self.PortBaseNames:
                constraints += self.define_contract_has_port_wname_constraints(contract, port_base_name)
        LOG.debug(constraints)
        return constraints


    def define_port_mapping_function(self, contract_uname_a, contract_uname_b):
        '''
        define mapping function
        '''
        contract_a = self.contracts_dict[contract_uname_a]
        contract_b = self.contracts_dict[contract_uname_b]

        mapping_f = z3.Function('%s_%s' % (contract_uname_a, contract_uname_b),
                                self.portc_types[contract_uname_a],
                                self.portc_types[contract_uname_b],
                                z3.BoolSort())

        self.mapping_functions[(contract_a, contract_b)] = mapping_f
        #and reverse
        self.mapping_functions[(contract_b, contract_a)] = mapping_f

        constraints = []

        #no outputs ports connected together
        for output_a in contract_a.output_ports_dict:
            for output_b in contract_b.output_ports_dict:
                constraints.append(mapping_f(output_a, output_b) == False)

        return constraints

    def synthetize(self, property_contract):
        '''
        perform synthesis process
        '''

        max_components = len(property_contract.output_ports_dict)

        for n in range(1, max_components):
            try:
                res = self.synthesize_fixed_size(property_contract, n)
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

        while True:
            try:
                candidate = self.synthesize_candidate(property_contract, size)
            except NotSynthesizableError as err:
                raise err
            else:
                try:
                    self.verify_candidate(candidate, property_contract)
                except NotSynthesizableError as err:
                    LOG.debug("candidate not valid")
                else:
                    return candidate

    def synthesize_candidate(self, property_contract, size):
        '''
        1) We need to create this variables and assert the possibilities
        2) We also need to create the mapping functions. Do we allow feedback? Not for now.
        3) We need to define the refinement relations, where possible. Low priority
        4) Verify and loop

        '''
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

