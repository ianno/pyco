'''
.. module:: contract_ex
:synopsis: This module contains an extension of the basci contracts defined in
            the pyco library

.. moduleauthor:: Antonio Iannopollo <antonio@berkeley.edu>

'''

from pyco.contract import Port as BasePort, Contract as BaseContract

import logging

LOG = logging.getLogger()

LOG.debug('In contract.py')

class Port(BasePort):
    '''
    This class extends the Port class from pyco.
    In addition to the base class, here every Port has a related SMT object.
    '''

    def __init__(self, base_name, literal=None, context=None):
        '''
        Override initializer. Add SMT port model
        '''
        super(Port, self).__init__(base_name, literal, context)
        


class Contract(BaseContract):
    '''
    Extends pyco.contract.Contract adding support
    for graphs and libraries
    '''

    def __init__(self, *args, **kwargs):
        '''
        Initialization
        '''

        super(Contract, self).__init__(*args, **kwargs)
