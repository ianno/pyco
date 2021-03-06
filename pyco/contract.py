'''
.. module:: contract_ex
:synopsis: This module contains an extension of the basci contracts defined in
            the pyco library

.. moduleauthor:: Antonio Iannopollo <antonio@berkeley.edu>

'''

from pycolite.contract import (Contract as BaseContract, PortMapping, CompositionMapping,
                           RefinementMapping, NotARefinementError)
from pycolite.parser.lexer import BaseSymbolSet

from pyco import LOG

LOG.debug('In contract.py')


# class Port(BasePort):
#    '''
#    This class extends the Port class from pycolite-lite-dev.
#    In addition to the base class, here every Port has a related SMT object.
#    '''
#
#    def __init__(self, base_name, contract=None, literal=None, context=None):
#        '''
#        Override initializer. Add SMT port model
#        '''
#        self.smt_model = None
#
#        super(Port, self).__init__(base_name, contract, literal, context)
#
#    def assign_to_solver(self, smt_manager):
#        '''
#        Registers port information to solver
#        '''
#        smt_manager.register_port(self)
#        self.smt_model = smt_manager.get_port_model(self)


class Contract(BaseContract):
    '''
    Extends pycolite-lite-dev.contract.Contract adding support
    for graphs and libraries
    '''
    ASSUMPTIONS = 'true'
    GUARANTEES = 'true'
    # pairs (name,type)
    INPUT_PORTS = []
    OUTPUT_PORTS = []

    def __init__(self, base_name, input_ports=None, output_ports=None,
                 assume_formula=None, guarantee_formula=None,
                 symbol_set_cls=BaseSymbolSet, context=None,
                 saturated=False, infer_ports=False):
        '''
        Initialization
        '''
        # pre-process
        for index, item in enumerate(self.INPUT_PORTS):
            try:
                (port_name, port_type) = item
            except ValueError:
                self.INPUT_PORTS[index] = (item, BaseType)

        for index, item in enumerate(self.OUTPUT_PORTS):
            try:
                (port_name, port_type) = item
            except ValueError:
                self.OUTPUT_PORTS[index] = (item, BaseType)

        self.port_type = {port_name: port_type for (port_name, port_type)
                          in self.INPUT_PORTS + self.OUTPUT_PORTS}
        # LOG.debug(self.port_type)

        if input_ports is None:
            input_ports = [port_name for (port_name, _) in self.INPUT_PORTS]
        if output_ports is None:
            output_ports = [port_name for (port_name, _) in self.OUTPUT_PORTS]
        if assume_formula is None:
            assume_formula = self.ASSUMPTIONS
        if guarantee_formula is None:
            guarantee_formula = self.GUARANTEES

        self.smt_model = None

        super(Contract, self).__init__(base_name, input_ports, output_ports,
                                       assume_formula, guarantee_formula,
                                       symbol_set_cls, context,
                                       saturated, infer_ports)

    def assign_to_solver(self, smt_manager):
        '''
        Registers contract information to solver
        '''
        smt_manager.register_contract(self)
        # self.smt_model = smt_manager.get_contract_model(self)

        for port in self.ports_dict.values():
            smt_manager.register_port(port)
            # port.assign_to_solver(smt_manager)


class DummyType(object):
    '''
    Implements base type for contract ports
    '''
    pass


class BaseType(DummyType):
    """
    Implements base type for contract ports
    """
    pass


class IntRangeType(BaseType):
    """
    Implements base type for contract ports
    """
    min = None
    max = None


class PortMappingError(Exception):
    '''
    Raised if a mapping constraint is add more than once
    '''
    pass


class NotATypeError(Exception):
    '''
    Raised if a type is not a subclass of BaseType
    '''

class EmptyContract(Contract):
    """
    An empty contract
    """
    INPUT_PORTS = []
    OUTPUT_PORTS = []
    ASSUMPTIONS = '''true'''
    GUARANTEES = 'true'