'''
This module contains the main interface to the SMT solver

Author: Antonio Iannopollo
'''

import logging
from pycox.z3_interface import Z3
from abc import abstractmethod

LOG = logging.getLogger()
LOG.debug('In solver_interface')


class SMTComponentManager(object):
    '''
    Class implementing a log which records a list of instantiated
    attribute (pyco.attribute.Attribute interface)
    '''

    base_names = {}
    unique_names = {}
    component_view = base_names.viewkeys()
    base_names_view = base_names.viewvalues()
    unique_names_view = unique_names.viewvalues()
    base_names_viewitems = base_names.viewitems()
    unique_names_viewitems = unique_names.viewitems()

    def register(self, component):
        '''
        Registers a object in the internal logs.
        The registered object, component, has to have base_name and unique_name
        attributes

        :param component: object with accessible base_name and unique_name
                          attributes (e.g. pyco.attribute.Attribute). Also,
                          component must be hashable
        '''

        self.base_names[component] = component.base_name
        self.unique_names[component] = component.unique_name

    @abstractmethod
    def get_smt_model(self, component):
        '''
        Returns the SMT representation of the component
        '''
        raise NotImplementedError()

class SMTPortManager(SMTComponentManager):
    '''
    Manage the interface between Ports and SMT
    '''

    def __init__(self):
        '''
        Defines init behavior, e.g. where to save list
        of parameters
        '''
        super(SMTPortManager, self).__init__()

    def get_smt_model(self, port):
        '''
        Returns the SMT representation of the port
        '''

        return Z3.create_port_model(port)

class SMTContractManager(SMTComponentManager):
    '''
    Manage the interface between Contracts and SMT
    '''

    def __init__(self):
        '''
        Defines init behavior, e.g. where to save list
        of parameters
        '''
        super(SMTContractManager, self).__init__()


    def get_smt_model(self, contract):
        '''
        Returns the MST representation of the contract
        '''
        return Z3.create_contract_model(contract)

class UnregisteredPortError(Exception):
    '''
    Exception raised in case a prot of a contract is not previously registered
    '''

#default interface
SMT_PORT_MANAGER = SMTPortManager()
SMT_CONTRACT_MANAGER = SMTContractManager()
