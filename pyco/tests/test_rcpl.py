'''
RCPL tests

Author: Antonio Iannopollo
'''

import pytest
from pyco.contract import Contract, NotARefinementError, CompositionMapping, RefinementMapping
from pyco.library import (LibraryComponent, ContractLibrary, LibraryPortMapping,
                          RefinementAssertionError,
                          EquivalentComponentError, LibraryCompositionMapping)
from pyco.tests.test_contracts import (TrueContract, FalseContract,
                                       FutureContract, NextContract)
import logging

LOG = logging.getLogger()

class A(Contract):
    '''
    G(a->Xb)
    '''
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['b']
    ASSUMPTIONS = 'true'
    GUARANTEES = 'G(a -> X b)'

class B(Contract):
    '''
    G(a->X!b)
    '''
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['b']
    ASSUMPTIONS = 'true'
    GUARANTEES = 'G(a -> X !b)'


class Meta(Contract):
    '''
    Fa -> Fb
    '''
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['b']
    ASSUMPTIONS = 'Fa'
    GUARANTEES = 'Fb'

class Spec(Contract):
    '''
    A: true, G: G(a -> (Fc & F!d )
    '''
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['c', 'd']
    ASSUMPTIONS = 'true'
    GUARANTEES = 'G(a -> (Fc & F!d ))'


@pytest.fixture()
def comp_a():
    '''
    A as component
    '''
    c_a = A('A')

    return LibraryComponent('A_comp', c_a)

@pytest.fixture()
def comp_b():
    '''
    B as component
    '''
    c_b = B('B')

    return LibraryComponent('B_comp', c_b)


@pytest.fixture()
def comp_ab(comp_a, comp_b):
    '''
       [A] -b1-
     /
    a
     \
       [B] -b2-
    '''
    mapping = LibraryCompositionMapping((comp_a, comp_b))
    mapping.composition_mapping.connect(comp_a.a, comp_b.a)
    mapping.composition_mapping.add(comp_a.b, 'b1')
    mapping.composition_mapping.add(comp_b.b, 'b2')

    return LibraryComponent('AB', (comp_a, comp_b), mapping=mapping)

@pytest.fixture()
def comp_meta():
    '''
    Meta as component
    '''
    meta = Meta('Meta')
    return LibraryComponent('META', meta)

@pytest.fixture()
def library():
    '''
    empty library
    '''
    return ContractLibrary('lib')

@pytest.fixture()
def populated_library(comp_a, comp_b, comp_ab, comp_meta, library):
    '''
    returns a populated library
    '''
    library.add(comp_a)
    library.add(comp_b)
    library.add(comp_ab)
    library.add(comp_meta)

    #add refinement assertion
    mapping = LibraryPortMapping([comp_ab, comp_meta])
    mapping.add(comp_ab.a, comp_meta.a)
    mapping.add(comp_ab.b1, comp_meta.b)

    comp_ab.add_refinement_assertion(comp_meta, mapping)

    return library

@pytest.fixture()
def valid_manual_design():
    '''
    use basic contracts to define design satisfiyng spec
    '''
    c_a = A('a_des')
    c_b = B('b_des')

    mapping = CompositionMapping([c_a, c_b])
    mapping.connect(c_a.a, c_b.a)
    mapping.add(c_a.b, 'b_a')
    mapping.add(c_b.b, 'b_b')

    c_ab = c_a.compose(c_b, new_name='design', composition_mapping=mapping)

    return c_ab

def test_populate_wrong(comp_a, comp_b, comp_ab, comp_meta, library):
    '''
    test library population as of fixture 'populate_library'
    '''
    library.add(comp_a)
    library.add(comp_b)
    library.add(comp_ab)
    library.add(comp_meta)

    #add refinement assertion
    mapping = LibraryPortMapping([comp_ab, comp_meta])
    mapping.add(comp_ab.a, comp_meta.a)
    mapping.add(comp_ab.b2, comp_meta.b)

    LOG.debug(comp_ab.contract)

    with pytest.raises(NotARefinementError):
        comp_ab.add_refinement_assertion(comp_meta, mapping)

    library.verify_library()
    assert True

def test_populate(comp_a, comp_b, comp_ab, comp_meta, library):
    '''
    test library population as of fixture 'populate_library'
    '''
    library.add(comp_a)
    library.add(comp_b)
    library.add(comp_ab)
    library.add(comp_meta)

    #add refinement assertion
    mapping = LibraryPortMapping([comp_ab, comp_meta])
    mapping.add(comp_ab.a, comp_meta.a)
    mapping.add(comp_ab.b1, comp_meta.b)

    LOG.debug(comp_ab.contract)

    comp_ab.add_refinement_assertion(comp_meta, mapping)

    library.verify_library()
    assert True

def test_rcp(valid_manual_design):
    '''
    Check spec pver manual_design
    '''
    spec = Spec('Spec')

    ref_map = RefinementMapping([spec, valid_manual_design])
    ref_map.add(spec.a, valid_manual_design.a)
    ref_map.add(spec.c, valid_manual_design.b_a)
    ref_map.add(spec.d, valid_manual_design.b_b)

    assert valid_manual_design.is_refinement(spec, ref_map)

def test_rcp_faulty_connection(valid_manual_design):
    '''
    Check spec pver manual_design
    '''
    spec = Spec('Spec')

    ref_map = RefinementMapping([spec, valid_manual_design])
    ref_map.add(spec.a, valid_manual_design.a)

    #inverted
    ref_map.add(spec.c, valid_manual_design.b_b)
    ref_map.add(spec.d, valid_manual_design.b_a)

    assert not valid_manual_design.is_refinement(spec, ref_map)


