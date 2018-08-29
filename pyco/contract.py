'''
.. module:: contract_ex
:synopsis: This module contains an extension of the basci contracts defined in
            the pyco library

.. moduleauthor:: Antonio Iannopollo <antonio@berkeley.edu>

'''

from pycolite.contract import (Contract as BaseContract, PortMapping, CompositionMapping,
                           RefinementMapping, NotARefinementError, NotDeterministicError)
from pycolite.parser.lexer import BaseSymbolSet
from pycolite.types import Bool, Int, Float, FrozenInt, FrozenBool
from pyco import LOG
import inspect

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
                if isinstance(item, (list, tuple)):
                    if len(item) >= 4:
                        pass
                else:
                    self.INPUT_PORTS[index] = (item, BaseTypeBool)

        for index, item in enumerate(self.OUTPUT_PORTS):
            try:
                (port_name, port_type) = item
            except ValueError:
                if isinstance(item, (list, tuple)):
                    if len(item) >= 4:
                        pass
                else:
                    self.OUTPUT_PORTS[index] = (item, BaseTypeBool)

        self.port_type = {}
        for t_elems in self.INPUT_PORTS + self.OUTPUT_PORTS:
            if inspect.isclass(t_elems[1]):
                self.port_type[t_elems[0]] = t_elems[1]
            else:
                self.port_type[t_elems[0]] = type(t_elems[1])

        # LOG.debug(self.port_type)


        # for each type, put together all ports with that type
        self.in_type_map = {p_type: set() for p_type in set([t[1] for t in self.INPUT_PORTS])}
        self.out_type_map = {p_type: set() for p_type in set([t[1] for t in self.OUTPUT_PORTS])}

        for t in self.INPUT_PORTS:
            name = t[0]
            p_type = t[1]
            self.in_type_map[p_type].add(name)

        for t in self.OUTPUT_PORTS:
            name = t[0]
            p_type = t[1]
            self.out_type_map[p_type].add(name)




        # LOG.debug(self.port_type)

        if input_ports is None:
            input_ports = [t for t in self.INPUT_PORTS]
        if output_ports is None:
            output_ports = [t for t in self.OUTPUT_PORTS]
        if assume_formula is None:
            assume_formula = self.ASSUMPTIONS
        if guarantee_formula is None:
            guarantee_formula = self.GUARANTEES


        super(Contract, self).__init__(base_name, input_ports, output_ports,
                                       assume_formula, guarantee_formula,
                                       symbol_set_cls, context,
                                       saturated, infer_ports)




    @property
    def type_map(self):
        '''
        return generic type map, without distinction between input and output
        :return:
        '''

        return dict(self.in_type_map.items() +
                    self.out_type_map.items())


    def assign_to_solver(self, smt_manager):
        '''
        Registers contract information to solver
        '''
        smt_manager.register_contract(self)
        # self.smt_model = smt_manager.get_contract_model(self)

        for port in self.ports_dict.values():
            smt_manager.register_port(port)
            # port.assign_to_solver(smt_manager)


# class DummyType(object):
#     '''
#     Implements base type for contract ports
#     '''
#     pass


class BaseTypeBool(Bool):
    """
    Implements base type for contract ports
    """
    pass

class ParameterBool(FrozenBool):
    """
    Implements parametric (frozen) bool
    """
    pass

class BaseTypeInt(Int):
    """
    Implements base type for contract ports
    """
    pass

class ParameterInt(FrozenInt):
    """
    Implements parametric (frozen) integer
    """
    pass


class BaseTypeFloat(Float):
    """
    Implements base type for contract ports
    """
    pass


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