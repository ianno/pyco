'''
Test synthesis process.
In this test we define a simple library of components,
and test the synthesis algorithms.

LIBRARY DESIGN
Library has three classes of components:
    1-1
    2-2
    2-3

the first class has two abstractions:
    G(a->Xb) - TODO: add types
    G(a->X!b)
2-2
    G(a&b -> c&d)
3-2
    G(a&b -> c&d)


TEST 1
In this case, we have a first spec with one input and one output.
we want the tool to find a single right component

TEST 2
Impossible spec

TEST 3
We want the tool to find a solution for a 2-2 spec, in which only
two 1-1 elements are suitable

Author: Antonio Iannopollo
'''

from pycox.contract import Contract
from pycox.library import (ContractLibrary, LibraryComponent,
                            LibraryPortMapping, LibraryCompositionMapping)
from pycox.synthesis import SynthesisInterface

import logging

LOG = logging.getLogger()

class A(Contract):
    '''
    G(a->Xb)
    '''
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['b']
    ASSUMPTIONS = 'GFa'
    GUARANTEES = 'G(a -> X b)'

class B(Contract):
    '''
    G(a->X!b)
    '''
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['b']
    ASSUMPTIONS = 'GFa'
    GUARANTEES = 'G(a -> X !b)'

class AB(Contract):
    '''
    G(a&b -> c&d)
    '''
    INPUT_PORTS = ['a', 'b']
    OUTPUT_PORTS = ['c', 'd']
    ASSUMPTIONS = 'GFa & GFb'
    GUARANTEES = 'G(a&b -> F(c&d))'

class ABC(Contract):
    '''
    G(a&b -> c&d)
    '''
    INPUT_PORTS = ['a', 'b', 'c']
    OUTPUT_PORTS = ['c', 'd']
    ASSUMPTIONS = 'GFa & GFb'
    GUARANTEES = 'G(a&b -> F(c&d))'

class Meta(Contract):
    '''
    Fa -> Fb
    '''
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['b']
    ASSUMPTIONS = 'Fa'
    GUARANTEES = 'Fb'

class Spec_1(Contract):
    '''
    A: GFa, G: G(a -> (Fc )
    '''
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['c']
    ASSUMPTIONS = 'GFa'
    GUARANTEES = 'G(a -> (Fc ))'

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
def comp_ab():
    '''
    AB as component
    '''
    c_b = AB('AB')

    return LibraryComponent('AB_comp', c_b)

@pytest.fixture()
def comp_ab():
    '''
    ABC as component
    '''
    c_b = AB('ABC')

    return LibraryComponent('ABC_comp', c_b)

@pytest.fixture()
def comp_ab_comp(comp_a, comp_b):
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

    return LibraryComponent('AB_composed', (comp_a, comp_b), mapping=mapping)

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

    library.verify_library()

    return library

def test_synthesis_0(populated_library):
    '''
    Perform basic synthesis test. Retrieve block from library
    '''

    spec = A('spec_A')

    synth_interface = SynthesisInterface(spec, populated_library)

    #synth_interface

    synth_interface.synthesize()

