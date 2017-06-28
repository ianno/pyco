'''
This module contains the main interface to the SMT solver

Author: Antonio Iannopollo
'''

from pyco import LOG

LOG.debug('In solver_interface')

class SMTManager(object):
    '''
    Manage the interface between Ports and SMT
    '''



    def __init__(self, library):
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
        self.library = library

        #if solver is None:
        #    solver = Z3Interface(library)

        #self.solver = solver



    def register_port(self, port):
        '''
        register a new port and returns a SMT based Port model

        :param port: Port to register
        :type port: pyco-dev.contract.Port
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

    #def get_port_model(self, port):
    #    '''
    #    returns port model
    #    '''
    #    return self.solver.create_port_model(port)

    #def get_contract_model(self, contract):
    #    '''
    #    returns contract model
    #    '''
    #    return self.solver.create_contract_model(contract)

    #def get_component_model(self, component):
    #    '''
    #    returns component model
    #    '''
    #    return self.solver.create_component_model(component)

    def _enumerate_names(self):
        '''
        returns all the names of components, contracts and ports
        '''
        port_names = self.port_name_pairs
        contract_names = self.contract_name_pairs
        component_names = self.component_name_pairs

        return (port_names, contract_names, component_names)

    @property
    def port_name_pairs(self):
        '''
        return port names
        '''
        return [(port.base_name, port.unique_name)
                for port in self.port_base_names.keys()]

    @property
    def contract_name_pairs(self):
        '''
        return contract names
        '''
        return [(contract.base_name, contract.unique_name)
                for contract in self.contract_base_names.keys()]

    @property
    def component_name_pairs(self):
        '''
        return component names
        '''
        return [(component.base_name, component.unique_name)
                for component in self.component_base_names.keys()]


class UnregisteredPortError(Exception):
    '''
    Exception raised in case a prot of a contract is not previously registered
    '''

#default interface
#SMT_NAME_MANAGER = SMTNameManager()
