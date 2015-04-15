'''
This module contains the implementation of classes and fucntions related
to the concept of library of contracts

Author: Antonio Iannopollo
'''
import logging
from pyco.attribute import Attribute
from pycox.contract import ContractMapping, PortMappingError, PortMapping

LOG = logging.getLogger()
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
        self.context = context
        self.name_attribute = Attribute(base_name, context)

    def add(self, library_component):
        '''
        add a library_component to the library object
        '''
        if library_component in self.components:
            raise ValueError()

        library_component.register_to_library(self)
        self.components.append(library_component)

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

    def __init__(self, base_name, contract, context=None):
        '''
        initialize component
        '''
        self.library = None
        self.contract = contract
        self.refinement_assertions = set()
        self.context = context
        self.name_attribute = Attribute(base_name, context)

    def register_to_library(self, library):
        '''
        Track who uses it
        '''
        self.library = library

    #def add_contract_instance(self, contract):
    #    '''
    #    Add a contract instance to the library component
    #    '''
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

        #get copies
        new_contracts, new_mapping = port_mapping.get_mapping_copies()

        local_contract = new_contracts[contract]
        other_contract = new_contracts[abstract_contract]

        #connect ports according to mapping relation
        for (port_a, port_b) in new_mapping.mapping:
            port_a.contract.connect_to_port(port_a, port_b)

        if not local_contract.is_refinement(other_contract):
            raise NotARefinementError(assertion)

        if enforce_strict:
            #error if refinemen also in the other direction
            if other_contract.is_refinement(local_contract):
                raise EquivalentComponentError(assertion)

        return


    def add_refinement_assertion(self, abstract_component, port_mapping=None, force_add=False):
        '''
        Add a refinement assetion.
        If force_add is True, this method raises an exception if abstract_library_component
        is not already in the library, otherwise it will be automatically added.
        '''
        if port_mapping is None:
            port_mapping = RefinementPortMapping(self.contract, abstract_component.contract)

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

#    def instantiate_composed_component(self):
#        '''
#        Create an instance of the library component
#        '''
#        #new_instances = [comp.copy() for comp in self.contracts.values()]
#
#        #new_contracts = {}
#        nctew_connections = set()
#        for unique_name,contract in self.contracts.items():
#            new_contracts[unique_name] = contract.copy()
#
#        for port_a, port_b in self.connections:
#            contract_uname_a = port_a.contract.unique_name
#            contract_uname_b = port_b.contract.unique_name
#
#            #get port for the new contract a and b
#            new_port_a = new_contracts[contract_uname_a].ports_dict[port_a.base_name]
#            new_port_b = new_contracts[contract_uname_b].ports_dict[port_b.base_name]
#
#            new_connections.add(new_port_a, new_port_b)
#
#        return (new_contracts, new_connections)

        #connect instances according to connection mapping
        #we need to reassign ports
        #...
#        composed = reduce(lambda x, y: x.compose(y), )

#       return composed.copy()

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



class RefinementPortMapping(object):
    '''
    Defines a port mapping to be used in checking refinement in library
    '''

    def __init__(self, contract, other_contract):
        '''
        initialize data structures
        '''

        if type(contract) is LibraryComponent:
            self.contract = contract.contract
        else:
            self.contract = contract

        if type(other_contract) is LibraryComponent:
            self.other_contract = other_contract.contract
        else:
            self.other_contract = other_contract

        self.contracts = (self.contract, self.other_contract)

        self.mapping = set()

    def _validate_port(self, port):
        '''
        Check if a port is properly assigned to the mapping
        '''
        if port.contract not in self.contracts:
            raise PortMappingError(port)

    def add(self, port_a, port_b):
        '''
        add a mapping pair to the list
        '''
        self._validate_port(port_a)
        self._validate_port(port_b)

        self.mapping.add((port_a, port_b))


    def get_mapping_copies(self):
        '''
        returns a copy of the contracts and an updated
        RefinementPortMapping object related to those copies

        :returns: a pair, in which the first element is a dictionary containing a reference
                  to the copied contracts, and a RefinementPortMapping object
        '''

        new_contracts = {}
        new_contracts[self.contract] = self.contract.copy()
        new_contracts[self.other_contract] = self.other_contract.copy()

        new_mapping = RefinementPortMapping(new_contracts[self.contract],
                                            new_contracts[self.other_contract])

        for (port_a, port_b) in self.mapping:
            new_mapping.add(new_contracts[port_a.contract].ports_dict[port_a.base_name],
                            new_contracts[port_b.contract].ports_dict[port_b.base_name])

        return (new_contracts, new_mapping)


PortMapping.register(RefinementPortMapping)


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



class NotARefinementError(Exception):
    '''
    Raised in case of wrong refinement assertion
    '''
    pass

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
