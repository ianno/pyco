'''
This module contains the main interface to the SMT solver

Author: Antonio Iannopollo
'''

import logging

LOG = logging.getLogger()
LOG.debug('In solver_interface')

class SMTPortManager(object):
    '''
    Manage the interface between Ports and SMT
    '''

    @classmethod
    def register_port(cls, port):
        '''
        register a new port and returns a SMT based Port model

        :param port: Port to register
        :type port: pycox.Port
        '''
        pass

