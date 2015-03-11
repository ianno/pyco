'''
This module includes the interface classes and functions for the Z3 SMT solver

Author: Antonio Iannopollo
'''

import logging
from pycox.smt_factory import SMTModelFactory
import z3
from pycox.solver_interface import SMT_PORT_MANAGER, SMT_CONTRACT_MANAGER

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
        pass

    def create_port_model(self, port):
        '''
        override from SMTModelFactory method
        '''
        pass

    def create_contract_model(self, contract):
        '''
        override from SMTModelFactory method
        '''
        pass

SMTModelFactory.register(Z3Interface)

#instance a public interface
Z3 = Z3Interface()

