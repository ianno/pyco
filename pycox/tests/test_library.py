'''
Library tests

Author: Antonio Iannopollo
'''

import pytest
from pycox.contract import Contract
from pycox.library import (LibraryComponent, ContractLibrary, LibraryPortMapping,
                           RefinementAssertionError, NotARefinementError, EquivalentComponentError)
from pycox.tests.test_contracts import (TrueContract, FalseContract,
                                        FutureContract, NextContract)
import logging

LOG = logging.getLogger()

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
    comp = LibraryComponent('test_c', truec)

    return comp

@pytest.fixture
def false_component():
    '''
    Creates a component for the False contract
    '''
    falsec = FalseContract('falsec')
    comp = LibraryComponent('false_comp', falsec)

    return comp

@pytest.fixture
def future_component():
    '''
    Returns a component containing a FutureContract
    '''

    futurec = FutureContract('futurec')
    comp = LibraryComponent('future_component', futurec)

    return comp

@pytest.fixture
def next_component():
    '''
    Returns a component containing a NextContract
    '''

    nextc = NextContract('nextc')
    comp = LibraryComponent('next_component', nextc)

    return comp

@pytest.fixture
def minimal_library(library, library_component, false_component, next_component, future_component):
    '''
    Returns a library with 4 elements, already in a hierarchy.
    Elements are TrueContract, FalseContract, FutureContract, NextContract
    '''

    library.add(library_component)
    library.add(false_component)
    library.add(next_component)
    library.add(future_component)

    mapping = LibraryPortMapping(next_component.contract, future_component.contract)
    mapping.add(next_component.contract.a, future_component.contract.a)
    mapping.add(next_component.contract.b, future_component.contract.x)

    next_component.add_refinement_assertion(future_component, mapping)

    #everything refines the TrueContract
    mapping_1 = LibraryPortMapping(false_component, library_component)
    mapping_1.add(library_component.a, false_component.c)
    mapping_1.add(library_component.b, false_component.d)
    false_component.add_refinement_assertion(library_component, mapping_1)

    mapping_2 = LibraryPortMapping(next_component, library_component)
    mapping_2.add(next_component.a, library_component.a)
    mapping_2.add(next_component.b, library_component.b)
    next_component.add_refinement_assertion(library_component, mapping_2)

    mapping_3 = LibraryPortMapping(future_component, library_component)
    mapping_3.add(future_component.a, library_component.a)
    mapping_3.add(future_component.x, library_component.b)
    future_component.add_refinement_assertion(library_component, mapping_3)

    #FalseContract refines everything
    mapping_4 = LibraryPortMapping(false_component, next_component)
    mapping_4.add(false_component.c, next_component.a)
    mapping_4.add(false_component.d, next_component.b)
    false_component.add_refinement_assertion(next_component, mapping_4)

    mapping_5 = LibraryPortMapping(false_component, future_component)
    mapping_5.add(false_component.c, future_component.a)
    mapping_5.add(false_component.d, future_component.x)
    false_component.add_refinement_assertion(future_component, mapping_5)

    return library

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


def test_refinement(future_component, next_component, library):
    '''
    Assert a true refinement relation and verifies it
    '''
    library.add(future_component)
    library.add(next_component)

    mapping = LibraryPortMapping(next_component.contract, future_component.contract)
    mapping.add(next_component.contract.a, future_component.contract.a)
    mapping.add(next_component.contract.b, future_component.contract.x)

    try:
        next_component.add_refinement_assertion(future_component, mapping)
    except:
        assert False
    else:
        assert True


def test_false_refinement(future_component, next_component, library):
    '''
    Assert a true refinement relation and verifies it
    '''
    library.add(future_component)
    library.add(next_component)

    mapping = LibraryPortMapping(next_component.contract, future_component.contract)
    mapping.add(next_component.contract.a, future_component.contract.a)
    mapping.add(next_component.contract.b, future_component.contract.x)

    with pytest.raises(NotARefinementError):
        future_component.add_refinement_assertion(next_component, mapping)

def test_not_in_lib(future_component, next_component, library):
    '''
    Assert a true refinement relation and verifies it
    '''
    library.add(next_component)

    mapping = LibraryPortMapping(next_component.contract, future_component.contract)
    mapping.add(next_component.contract.a, future_component.contract.a)
    mapping.add(next_component.contract.b, future_component.contract.x)

    with pytest.raises(ValueError):
        next_component.add_refinement_assertion(future_component, mapping)

def test_equivalent(next_component, library):
    '''
    Assert a true refinement relation and verifies it
    '''
    library.add(next_component)

    mapping = LibraryPortMapping(next_component.contract, next_component.contract)
    mapping.add(next_component.contract.a, next_component.contract.a)
    mapping.add(next_component.contract.b, next_component.contract.b)

    with pytest.raises(EquivalentComponentError):
        next_component.add_refinement_assertion(next_component, mapping)


def test_verify_library(minimal_library):
    '''
    Perform a library self test
    '''

    try:
        minimal_library.verify_library()
    except Exception as err:
        LOG.debug('test_verify_library error!')
        LOG.debug(type(err))
        assert False
    else:
        assert True
