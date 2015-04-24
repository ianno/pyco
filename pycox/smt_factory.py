'''
This module contains an abstraction of the operations performed
by a SMT solver in pycox.
Classes in this module are used to implement the strategy design pattern.
'''

import logging
from abc import ABCMeta, abstractmethod

LOG = logging.getLogger()
LOG.debug('In SMT_strategies')

class SMTModelFactory:
    '''
    Abstract Class defining the set of operations to create SMT based models
    '''

    __metaclass__ = ABCMeta

    @abstractmethod
    def create_port_model(self, port):
        '''
        Given a Port, create a SMT port model for the same object
        '''
        pass

    @abstractmethod
    def create_contract_model(self, contract):
        '''
        Given a Contract object, create a SMT contract model
        '''
        pass

    @abstractmethod
    def create_component_model(self, component):
        '''
        Given a LibraryComponent object, creat a SMT component model
        '''
        pass
