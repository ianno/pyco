'''
.. module:: contract_ex
:synopsis: This module contains an extension of the basci contracts defined in
            the pyco library

.. moduleauthor:: Antonio Iannopollo <antonio@berkeley.edu>

'''

from pyco.contract import Port as BasePort, Contract as BaseContract
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
                 saturated=True):
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


class ContractMapping(object):
    '''
    This class stores the information about mapping a certain number
    of ports of a contract to another.
    This can be seen as a generalization of the concept of port conncetion.
    The main difference is that while the connection is a strong bond among
    contracts (e.g. a design constraint), a mapping relation is a loose
    reference, used in verification and synthesis, where a connection is not
    a absolute constraint and can be modified or deleted.
    '''

    def __init__(self, contract_a, contract_b):
        '''
        Instantiate a mapping constraint.

        :param contract_a: instance or class of type Contract
        :param contract_b: instance or class of type Contract
        '''
        self.contract_a = contract_a
        self.contract_b = contract_b

        self.mapping = set()
        '''
        mapping is a list of pairs, which are port
        base_names who needs to be equivalent.
        '''

    def _validate_ports(self, port_a, port_b):
        '''
        raises an exception if port is not related to one of the mapped contract
        '''
        if (port_a.contract is not self.contract_a) or (port_b.contract is not self.contract_b):
            raise PortMappingError()

    def add(self, port_a, port_b):
        '''
        Add a map constraint between ports in contract_a and contract_b.

        :param base_name_a: base_name of port in contract_a
        :param base_name_b: base_name of port in contract_b
        '''
        self._validate_ports(port_a, port_b)
        self.mapping.add((port_a, port_b))



class PortMappingError(Exception):
    '''
    Raised if a mapping constraint is add more than once
    '''
    pass



