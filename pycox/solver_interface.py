'''
This module contains the main interface to the SMT solver

Author: Antonio Iannopollo
'''

import logging
from pycox.z3_interface import Z3

LOG = logging.getLogger()
LOG.debug('In solver_interface')

class SMTNameManager(object):
    '''
    Manage the interface between Ports and SMT
    '''



    def __init__(self, solver=Z3):
        '''
        Defines init behavior, e.g. where to save list
        of parameters
        '''
        self.port_base_names = {}
        self.port_unique_names = {}
        self.contract_base_names = {}
        self.contract_unique_names = {}
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


class UnregisteredPortError(Exception):
    '''
    Exception raised in case a prot of a contract is not previously registered
    '''

#default interface
SMT_PORT_MANAGER = SMTNameManager()
