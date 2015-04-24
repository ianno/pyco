'''
This module contains the main interface to the SMT solver

Author: Antonio Iannopollo
'''

import logging
from pycox.z3_interface import Z3Interface

LOG = logging.getLogger()
LOG.debug('In solver_interface')

class SMTManager(object):
    '''
    Manage the interface between Ports and SMT
    '''



    def __init__(self, solver=None):
        '''
        Defines init behavior, e.g. where to save list
        of parameters
        '''
        self.port_base_names = {}
        self.port_unique_names = {}
        self.contract_base_names = {}
        self.contract_unique_names = {}
        self.component_base_names = {}
        self.component_unique_names = {}

        if solver is None:
            solver = Z3Interface()

        self.solver = solver



    def register_port(self, port):
        '''
        register a new port and returns a SMT based Port model

        :param port: Port to register
        :type port: pycox.contract.Port
        '''
        self.port_base_names[port] = port.base_name
        self.port_unique_names[port] = port.unique_name


    def register_contract(self, contract):
        '''
        register a new contract and return a SMT based contract model

        :param contract: the Contract object to be registerd
        :type contract: pycox.contract.Contract
        '''

        self.contract_base_names[contract] = contract.base_name
        self.contract_unique_names[contract] = contract.unique_name

    def register_component(self, component):
        '''
        register a new component and return a SMT based contract model

        :param contract: the LibraryComponent object to be registerd
        :type contract: pycox.library.LibraryComponent
        '''

        self.component_base_names[component] = component.base_name
        self.component_unique_names[component] = component.unique_name

    def get_port_model(self, port):
        '''
        returns port model
        '''
        return self.solver.create_port_model(port)

    def get_contract_model(self, contract):
        '''
        returns contract model
        '''
        return self.solver.create_contract_model(contract)

    def get_component_model(self, component):
        '''
        returns component model
        '''
        return self.solver.create_component_model(component)

    def _enumerate_names(self):
        '''
        returns all the names of components, contracts and ports
        '''
        port_names = [(port.base_name, port.unique_name)
                      for port in self.port_base_names.keys()]
        contract_names = [(contract.base_name, contract.unique_name)
                          for contract in self.contract_base_names.keys()]
        component_names = [(component.base_name, component.unique_name)
                           for component in self.component_base_names.keys()]

        return (port_names, contract_names, component_names)



class UnregisteredPortError(Exception):
    '''
    Exception raised in case a prot of a contract is not previously registered
    '''

#default interface
#SMT_NAME_MANAGER = SMTNameManager()
