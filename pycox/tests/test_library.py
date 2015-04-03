'''
Library tests

Author: Antonio Iannopollo
'''

import pytest
from pycox.contract import Contract
from pycox.library import LibraryComponent, ContractLibrary
from pycox.tests.test_contracts import TrueContract, FalseContract


@pytest.fixture
def library():
    '''
    returns an empty library
    '''
    return ContractLibrary('libTest')

@pytest.fixture
def library_component():
    '''
    Create a library component with only a single contract in it
    '''

    truec = TrueContract('truec')
    comp = LibraryComponent()
    comp.add_contract_instance(truec)

    return comp

@pytest.fixture
def false_component():
    '''
    Creates a component for the False contract
    '''
    falsec = FalseContract('falsec')
    comp = LibraryComponent()
    comp.add_contract_instance(falsec)

    return comp

def test_library_add(library_component, library):
    '''
    Test construction of a library woth only a single component
    '''

    print 'test library c'
    print library_component

    library.add(library_component)
    assert True

def test_library_verification_basic(library_component, false_component, library):
    '''
    Asserts a refinement relation and verifies library
    '''
    library.add(library_component)
    library.add(false_component)

    

