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

    def __init__(self):
        '''
        init
        '''
        self.ComponentBaseName = None
        self.ComponentUniqueName = None
        self.PortBaseName = None
        self.PortUniqueName = None
        self.ContractBaseName = None
        self.ContractUniqueName = None

        self.ZPort = None

    def create_port_model(self, port):
        '''
        override from SMTModelFactory method
        '''
        pass

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

        return  self.ZContract.contract(CBaseNames[0], CUniqueNames[0], port_list, PortList.bottom)


    def create_component_model(self, component):
        '''
        override from SMTModelFactory method
        '''
        pass

    def create_z3_environment(self, ports, contracts, components):
        '''
        Creates basic types for the current library instance
        '''

        #component names
        #(self.ComponentBaseName,
        # self.ComponentBaseNames) = z3.EnumSort('ComponentBaseName', [name[0] for name in components])
        #(self.ComponentUniqueName,
        # self.ComponentUniqueNames) = z3.EnumSort('ComponentUniqueName', [name[1] for name in components])

        #(self.ContractBaseName,
        # self.ContractBaseNames) = z3.EnumSort('ContractBaseName', [name[0] for name in contracts])
        #(self.ContractUniqueName,
        # self.ContractUniqueNames) = z3.EnumSort('ContractUniqueName', [name[1] for name in contracts])

        #(self.PortBaseName,
        # self.PortBaseNames) = z3.EnumSort('PortBaseName', [name[0] for name in ports])
        #(self.PortUniqueName,
        # self.PortUniqueNames) = z3.EnumSort('PortUniqueName', [name[1] for name in ports])


        #component names
        (base_names, unique_names) = zip(*components)

        self.ComponentBaseName = z3.Datatype('ComponentBaseName')
        _ = [self.ComponentBaseName.declare(x) for x in set(base_names)]
        self.ComponentBaseName = self.ComponentBaseName.create()

        self.ComponentUniqueName = z3.Datatype('ComponentUniqueName')
        _ = [self.ComponentUniqueName.declare(x) for x in set(unique_names)]
        self.ComponentUnique = self.ComponentUniqueName.create()

        #contract names
        (base_names, unique_names) = zip(*contracts)

        self.ContractBaseName = z3.Datatype('ContractBaseName')
        _ = [self.ContractBaseName.declare(x) for x in set(base_names)]
        self.ContractBaseName = self.ContractBaseName.create()

        self.ContractUniqueName = z3.Datatype('ContractUniqueName')
        _ = [self.ContractUniqueName.declare(x) for x in set(unique_names)]
        self.ContractUnique = self.ContractUniqueName.create()

        #port names
        (base_names, unique_names) = zip(*ports)

        self.PortBaseName = z3.Datatype('PortBaseName')
        _ = [self.PortBaseName.declare(x) for x in  set(base_names)]
        self.PortBaseName = self.PortBaseName.create()

        self.PortUniqueName = z3.Datatype('PortUniqueName')
        _ = [self.PortUniqueName.declare(x) for x in set(unique_names)]
        self.PortUnique = self.PortUniqueName.create()


        self.ZPort = z3.Datatype('ZPort')
        self.ZPort.declare('port',
                     ('base_name', self.PortBaseName),
                     ('unique_name', self.PortUniqueName))

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
                          ('input_ports', self.ZPortList),
                          ('output_ports', self.ZPortList))

        self.ZContract = self.ZContract.create()

        self.ZContractList = z3.Datatype('ZContractList')
        self.ZContractList.declare('node', ('elem', self.ZContract), ('tail', self.ZContractList))
        self.ZContractList.declare('bottom')

        self.ZComponent = z3.Datatype('ZComponent')
        self.ZComponent.declare('component',
                           ('base_name', self.ComponentBaseName),
                           ('unique_name', self.ComponentUniqueName),
                           ('contracts', self.ZContractList))


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
        self.component_has_contract_wbase_name = z3.Function('component_has_contract_wbase_name',
                                                             self.ZComponent,
                                                             self.ContractBaseName,
                                                             z3.BoolSort())
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


SMTModelFactory.register(Z3Interface)

#instance a public interface
Z3 = Z3Interface()

