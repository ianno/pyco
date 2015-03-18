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
        pass


class LibraryComponent(object):
    '''
    Taken a single or a composition of contracts,
    store all the informations related to the composition.

    TODO?:(Implements the Observer pattern to allow an easy propagation of
    the refinement information once inferred)
    '''

    def __init__(self):
        '''
        initialize component
        '''
        self.contracts = {}
        self.connections = []

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

        self.connections.append(ConnectionConstraint(contract_a, contract_b, port_a, port_b))

        #connect the contracts
        contract_b.connect(port_b, contract_a, port_a)

    def instantiate_composed_component(self):
        '''
        Create an instance of the library component
        '''
        composed = reduce(lambda x, y: x.compose(y), self.contracts.values())
        return composed



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

