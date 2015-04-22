'''
.. module:: contract_ex
:synopsis: This module contains an extension of the basci contracts defined in
            the pyco library

.. moduleauthor:: Antonio Iannopollo <antonio@berkeley.edu>

'''

from pyco.contract import (Port as BasePort, Contract as BaseContract, PortMapping,
                           CompositionMapping, RefinementMapping as ContractMapping,
                           NotARefinementError)
from pyco.parser.lexer import BaseSymbolSet
import logging
from pycox.solver_interface import SMT_PORT_MANAGER

LOG = logging.getLogger()

LOG.debug('In contract.py')

class Port(BasePort):
    '''
    This class extends the Port class from pyco.
    In addition to the base class, here every Port has a related SMT object.
    '''

    def __init__(self, base_name, contract=None, literal=None, context=None):
        '''
        Override initializer. Add SMT port model
        '''
        super(Port, self).__init__(base_name, contract, literal, context)
        SMT_PORT_MANAGER.register_port(self)
        self.smt_model = SMT_PORT_MANAGER.get_port_model(self)


class Contract(BaseContract):
    '''
    Extends pyco.contract.Contract adding support
    for graphs and libraries
    '''
    ASSUMPTIONS = ''
    GUARANTEES = ''
    INPUT_PORTS = []
    OUTPUT_PORTS = []

    def __init__(self, base_name, input_ports=None, output_ports=None,
                 assume_formula=None, guarantee_formula=None,
                 symbol_set_cls=BaseSymbolSet, context=None,
                 saturated=False):
        '''
        Initialization
        '''
        if input_ports is None:
            input_ports = self.INPUT_PORTS
        if output_ports is None:
            output_ports = self.OUTPUT_PORTS
        if assume_formula is None:
            assume_formula = self.ASSUMPTIONS
        if guarantee_formula is None:
            guarantee_formula = self.GUARANTEES

        super(Contract, self).__init__(base_name, input_ports, output_ports,
                                       assume_formula, guarantee_formula,
                                       symbol_set_cls, context,
                                       saturated)

        SMT_PORT_MANAGER.register_contract(self)
        self.smt_model = SMT_PORT_MANAGER.get_contract_model(self)




class PortMappingError(Exception):
    '''
    Raised if a mapping constraint is add more than once
    '''
    pass



