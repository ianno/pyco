'''
This module contains the implementation of classes and fucntions related
to the concept of library of contracts

Author: Antonio Iannopollo
'''
from pyco.attribute import Attribute
from pycox.contract import (ContractMapping, PortMappingError, PortMapping,
                            CompositionMapping, NotARefinementError, BaseType,
                            NotATypeError)

from pycox.solver_interface import SMTManager
from pycox import LOG

LOG.debug('in library')

class ContractLibrary(object):
    '''
    Implementation of the library of contracts
    '''

    def __init__(self, base_name, context=None):
        '''
        initializer
        '''
        self.components = []

        #type structures
        self.typeset = set()
        self.typeset.add(BaseType)

        self._type_compatibility_set = set()

        self.hierarchy = {}
        self.refines = {}
        self.refined_by = {}

        self.context = context
        self.name_attribute = Attribute(base_name, context)

        self.smt_manager = SMTManager(self)

    @property
    def max_hierarchy(self):
        '''
        computes the highest level of hierarchy
        '''
        if not self.hierarchy:
            return 0

        return max(self.hierarchy.values())

    def _new_refinement_assertion(self, assertion):
        '''
        register a new refinement assertion
        '''
        #TODO: check types
        concrete = assertion.component.contract
        abstract = assertion.abstract_component.contract
        mapping = assertion.port_mapping


        self.hierarchy[concrete.base_name] = self.hierarchy[abstract.base_name]+1
        if concrete.base_name not in self.refined_by:
            self.refined_by[concrete.base_name] = {}
        self.refined_by[concrete.base_name][abstract.base_name] = {}

        if abstract.base_name not in self.refines:
            self.refines[abstract.base_name] = {}
        self.refines[abstract.base_name][concrete.base_name] = {}

        for port_a, port_b in mapping.mapping:
            if port_a.contract == concrete:
                self.refined_by[concrete.base_name][abstract.base_name][port_a.base_name] = port_b.base_name
                self.refines[abstract.base_name][concrete.base_name][port_b.base_name] = port_a.base_name
            else:
                self.refined_by[concrete.base_name][abstract.base_name][port_b.base_name] = port_a.base_name
                self.refines[abstract.base_name][concrete.base_name][port_a.base_name] = port_b.base_name


    @property
    def type_compatibility_set(self):
        '''
        Returns BaseType-BaseType if the set is empty
        '''
        if not self._type_compatibility_set:
            return set([(BaseType, BaseType)])
        else:
            return self._type_compatibility_set

    def add(self, library_component):
        '''
        add a library_component to the library object
        '''
        if library_component in self.components:
            raise ValueError()

        library_component.register_to_library(self)
        library_component.assign_to_solver(self.smt_manager)

        self.components.append(library_component)
        self.hierarchy[library_component.contract.base_name] = 0

    def add_type(self, type_cls):
        '''
        add a type class to the list
        '''
        if not issubclass(type_cls, BaseType):
            raise NotATypeError(type_cls)

        self.typeset.add(type_cls)

        #given the new type, compute new compatibilities
        #according to the actual ones
        addition = set()
        for (type_a, type_b) in self._type_compatibility_set:
            #if (a, b) in the set, then also (b, a) is in
            #by constraction
            if issubclass(type_cls, type_a):
                addition.add((type_cls, type_b))
                addition.add((type_b, type_cls))

        self._type_compatibility_set = self._type_compatibility_set | addition


    def add_type_compatibility(self, type_a, type_b):
        '''
        add a pair of compatible types
        '''
        if (type_a not in self.typeset or
            type_b not in self.typeset):
            raise UndefinedTypeError((type_a, type_b))

        self._type_compatibility_set.add((type_a, type_b))
        self._type_compatibility_set.add((type_b, type_a))

        #add compatibility also for subclasses
        for a_type in self.typeset:
            if issubclass(a_type, type_a):
                self._type_compatibility_set.add((a_type, type_b))
                self._type_compatibility_set.add((type_b, a_type))
            if issubclass(a_type, type_b):
                self._type_compatibility_set.add((a_type, type_a))
                self._type_compatibility_set.add((type_a, a_type))


    def verify_library(self):
        '''
        Verifies that all the relations in the library are consistent
        '''
        for component in self.components:
            try:
                component.verify_refinement_assertions()
            except NotARefinementError as error:
                LOG.debug('in verify_library')
                LOG.debug(error)
                raise error

    def __contains__(self, item):
        '''
        Overrides 'in' operator
        '''
        if item in self.components:
            return True
        else:
            return False


    def verify_property(self, design_contract, property_contract, port_mapping):
        '''
        Returns True if design_contract refines property_contract, according to
        the given mapping.
        Implements RCPL algorithm
        '''
        pass

    def verify_property_rcp(self, design_contract, property_contract, port_mapping):
        '''
        Low efficiency version of verify_property. Implememtns the RCP algorithm
        '''
        pass

    def synthesize_design(self, partial_design, property_contract, port_mapping):
        '''
        Returns a new composition of contracts from the library which
        is consistent and compatible and refines property_contract
        '''
        pass



class LibraryComponent(object):
    '''
    Taken a single or a composition of contracts,
    store all the informations related to the composition.

    TODO?:(Implements the Observer pattern to allow an easy propagation of
    the refinement information once inferred)
    '''

    def __init__(self, base_name, components, mapping=None, context=None):
        '''
        initialize component
        '''
        self.library = None
        self.mapping = mapping
        try:
            self.components = set(components)
            self._contracts = None
            self.contract = self.get_composite_instance()
        except TypeError as e:
            #print e
            #it is a single contract instead of a list
            self._contracts = set()
            self._contracts.add(components)
            self.contract = components.copy()
            self.components = None

        self.refinement_assertions = set()
        self.context = context

        self.name_attribute = Attribute(base_name, self.context)

        self.smt_model = None

    def assign_to_solver(self, smt_manager):
        '''
        Registers component information to solver
        '''
        smt_manager.register_component(self)
        #self.smt_model = smt_manager.get_component_model(self)

        self.contract.assign_to_solver(smt_manager)


    @property
    def base_name(self):
        '''
        returns component's base_name
        '''
        return self.name_attribute.base_name

    @property
    def unique_name(self):
        '''
        returns component's unique_name
        '''
        return self.name_attribute.unique_name

    def register_to_library(self, library):
        '''
        Track who uses it
        '''
        self.library = library

    def get_composite_instance(self):
        '''
        Returns a new contract created by composing all
        the contracts associated to the component
        '''
        (new_contracts, new_mapping) = self.mapping.get_mapping_copies()

        contracts = set(new_contracts.viewvalues())

        root = contracts.pop()

        return root.compose(contracts, composition_mapping=new_mapping)

    #def add_contract_instance(self, contract):
    #    '''
    #    Add a contract instance to the library component
    #    self.contracts[contract.unique_name] = contract

    #    self.contracts[contract.unique_name] = contract
    #def add_connection(self, port_a, port_b):
    #    '''
    #    Define a new connection between two contracts
    #    '''
    #    if (port_a.contract not in self.contracts.values() or
    #            port_b.contract not in self.contracts.values()):
    #        raise KeyError()

    #    self.connections.add(port_a, port_b)

    #    #connect the contracts
    #    #not now, done once we request a new instance
    #    #contract_b.connect_to_port(port_b, contract_a, port_a)


    def verify_refinement(self, assertion, enforce_strict=False):
        '''
        verify a refinement assertion.
        If enforce_strict is true, a EquivalentComponentError will be raised
        if the two contracts are equivalent
        '''

        if self is not assertion.component:
            raise RefinementAssertionError(assertion)

        port_mapping = assertion.port_mapping
        contract = assertion.component.contract
        abstract_contract = assertion.abstract_component.contract

        if not contract.is_refinement(abstract_contract, refinement_mapping=port_mapping):
            raise NotARefinementError(assertion)

        if enforce_strict:
            #error if refinemen also in the other direction
            if abstract_contract.is_refinement(contract, refinement_mapping=port_mapping):
                raise EquivalentComponentError(assertion)

        return


    def add_refinement_assertion(self, abstract_component, port_mapping=None, force_add=False):
        '''
        Add a refinement assetion.
        If force_add is True, this method raises an exception if abstract_library_component
        is not already in the library, otherwise it will be automatically added.
        '''
        if port_mapping is None:
            port_mapping = LibraryPortMapping([self.contract, abstract_component.contract])

        if ((self.contract not in port_mapping.contracts) or
                (abstract_component.contract not in port_mapping.contracts)):
            raise PortMappingError(port_mapping)

        assertion = RefinementAssertion(self, abstract_component, port_mapping)

        try:
            self.verify_refinement(assertion, enforce_strict=True)
        except NotARefinementError as err:
            raise err
        except EquivalentComponentError as err:
            raise err
        else:
            #if the refinement is verified, we can check we have the block in the library
            if abstract_component not in self.library:
                if force_add:
                    self.library.add(abstract_component)
                else:
                    raise ValueError()

            #save assertion
            self.refinement_assertions.add(assertion)
            self.library._new_refinement_assertion(assertion)

    def verify_refinement_assertions(self):
        '''
        Runs a verification of all the refinement registered assertions
        '''

        for assertion in self.refinement_assertions:
            try:
                self.verify_refinement(assertion)
            except NotARefinementError as err:
                LOG.debug('here')
                LOG.debug(assertion)
                raise err

        return

    @property
    def contracts(self):
        '''
        Returns a set of contracts taken from the associate components
        '''
        if self._contracts is None:
            self._contracts = set([comp.contract for comp in self.components])

        return self._contracts

    def __getattr__(self, port_name):
        '''
        Checks if port_name is in ports_dict and consider it as a Contract attribute.
        IF it is present, returns the
        requested port, otherwise raises a AttributeError exception
        '''

        if port_name in self.contract.ports_dict:
            return self.contract.ports_dict[port_name]
        else:
            raise AttributeError



class RefinementAssertion(object):
    '''
    Store a refinement assertion
    '''

    def __init__(self, component, abstract_component, port_mapping):
        '''
        Stores the information
        '''
        self.component = component
        self.abstract_component = abstract_component
        self.port_mapping = port_mapping

        self.verify_assertion()

    def verify_assertion(self):
        '''
        verify valid assertion.
        Raises an exception in case of malformed assertion
        '''

        if ((self.component.contract not in self.port_mapping.contracts) or
                (self.abstract_component.contract not in self.port_mapping.contracts)):

            raise PortMappingError(self)



class LibraryCompositionMapping(object):
    '''
    Adapts CompositionMapping for library and components
    '''

    def __init__(self, components, context=None):
        '''
        Extract contracts from components
        '''
        self.components = components

        self.composition_mapping = CompositionMapping([component.contract
                                                       for component in components],
                                                      context)
        return


    def get_mapping_copies(self):
        '''
        returns a copy of the contracts and an updated
        LibraryPortMapping object related to those copies

        :returns: a pair, in which the first element is a dictionary containing a reference
                  to the copied contracts, and a LibraryPortMapping object
        '''

        new_contracts = {contract: contract.copy()
                         for contract in self.composition_mapping.contracts}

        new_mapping = CompositionMapping(new_contracts.viewvalues())


        for mapped_name, ports in self.composition_mapping.mapping.viewitems():
            for port in ports:
                new_mapping.add(new_contracts[port.contract].ports_dict[port.base_name],
                                mapped_name)

        return (new_contracts, new_mapping)




class LibraryPortMapping(ContractMapping):
    '''
    Defines a port mapping to be used in checking refinement in library
    '''

    def __init__(self, components):
        '''
        initialize data structures
        '''
        self.components = set()

        try:
            iterator = iter(components)
        except TypeError:
            #if there is only one element
            iterator = iter([components])

        contracts = set()

        for component in iterator:
            if type(component) is LibraryComponent:
                contracts.add(component.contract)
                self.components.add(component)
            else:
                contracts.add(component)

        super(LibraryPortMapping, self).__init__(contracts)


PortMapping.register(LibraryPortMapping)


#class ConnectionConstraint(object):
#    '''
#    Store info related to a connection constraint
#    '''
#
#    def __init__(self, port_a, port_b):
#        '''
#        initialize
#        '''
#        self.contract_a = port_a.contract
#        self.contract_b = port_b.contract
#        self.port_a = port_a
#        self.port_b = port_b
#
#    def connected_contract_unique_names(self):
#        '''
#        returns a tuple containing the names of connected contracts
#        '''
#        return (self.contract_a.unique_name, self.contract_b.unique_name)



class RefinementAssertionError(Exception):
    '''
    Raised in case of errors related to refinement assertions
    '''
    pass

class EquivalentComponentError(Exception):
    '''
    Raised if a component is equivalent to the another one in defining
    a refinement assertion
    '''
    pass


class UndefinedTypeError(Exception):
    '''
    Raised if trying to use a type not registered in the library
    '''

