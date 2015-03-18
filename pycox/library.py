'''
This module contains the implementation of classes and fucntions related
to the concept of library of contracts

Author: Antonio Iannopollo
'''

class ContractLibrary(object):
    '''
    Implementation of the library of contracts
    '''

    def __init__(self):
        '''
        initializer
        '''
        self.components = []

    def add(self, library_component):
        '''
        add a library_component to the library object
        '''
        if library_component in self.components:
            raise ValueError()

        self.components.append(library_component)

    def verify_library(self):
        '''
        Verifies that all the relations in the library are consistent
        '''
        for component in self.components:
            try:
                component.verify_refinement_assetions()
            except NotARefinementError as error:
                raise error

    def __contains__(self, item):
        '''
        Overrides 'in' operator
        '''
        if item in self.components:
            return True
        else:
            return False



class LibraryComponent(object):
    '''
    Taken a single or a composition of contracts,
    store all the informations related to the composition.

    TODO?:(Implements the Observer pattern to allow an easy propagation of
    the refinement information once inferred)
    '''

    def __init__(self, library):
        '''
        initialize component
        '''
        self.library = library
        self.contracts = {}
        self.connections = set()
        self.refinement_assertions = set()

    def add_contract_instance(self, contract):
        '''
        Add a contract instance to the library component
        '''
        self.contracts[contract.unique_name] = contract

    def add_connection(self, contract_a, contract_b, port_a, port_b):
        '''
        Define a new connection between two contracts
        '''
        if (contract_a not in self.contracts.values() or
                contract_b not in self.contracts.values()):
            raise KeyError()

        self.connections.add(ConnectionConstraint(contract_a, contract_b, port_a, port_b))

        #connect the contracts
        contract_b.connect_to_port(port_b, contract_a, port_a)

    def add_refinement_assertion(self, abstract_library_component, force_add=False):
        '''
        Add a refinement assetion.
        If force_add is True, this method raises an exception if abstract_library_component
        is not already in the library, otherwise it will be automatically added.
        '''
        #verify refinement before asserting
        local_composition = self.instantiate_composed_component()
        other_composition = abstract_library_component.instantiate_composed_component()

        if local_composition.is_refinement(other_composition):

            #if the refinement is verified, we can check we have the block in the library
            if abstract_library_component not in self.library:
                if force_add:
                    self.library.add(abstract_library_component)
                else:
                    raise ValueError()

            self.refinement_assertions.add(abstract_library_component)

        else:
            raise NotARefinementError((self, abstract_library_component))

    def instantiate_composed_component(self):
        '''
        Create an instance of the library component
        '''
        if len(self.contracts) == 1:
            composed = self.contracts[0]
        else:
            composed = reduce(lambda x, y: x.compose(y), self.contracts.values())

        return composed

    def verify_refinement_assertions(self):
        '''
        Runs a verification of all the refinement registered assertions
        '''

        local_composition = self.instantiate_composed_component()

        for abstract in self.refinement_assertions:

            if not local_composition.is_refinement(abstract.instantiate_commposed_component()):
                raise NotARefinementError((self, abstract))

        return True

class ConnectionConstraint(object):
    '''
    Store info related to a connection constraint
    '''

    def __init__(self, contract_a, contract_b, port_a_name, port_b_name):
        '''
        initialize
        '''
        self.contract_a = contract_a
        self.contract_b = contract_b
        self.port_a = port_a_name
        self.port_b = port_b_name

    def connected_contract_unique_names(self):
        '''
        returns a tuple containing the names of connected contracts
        '''
        return (self.contract_a.unique_name, self.contract_b.unique_name)

class NotARefinementError(Exception):
    '''
    Raised in case of wrong refinement assertion
    '''
    pass
