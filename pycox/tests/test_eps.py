'''
test_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
It uses files from pycox/examples/example_eps
Add reference

Author: Antonio Iannopollo
'''


import pytest
from pycox.examples.example_eps import *

@pytest.fixture
def abstr_gen():
    '''
    abstract generator
    '''
    comp = AbstractGenerator('AbstractGen')
    return LibraryComponent('AbstrGenC', comp)

@pytest.fixture
def dumb_gen():
    '''
    dumb generator
    '''
    comp = DumbGenerator('DumbGen')
    return LibraryComponent('DumbGenC', comp)

@pytest.fixture
def std_gen():
    '''
    std generator
    '''
    comp = StdGenerator('StdGen')
    return LibraryComponent('StdGenC', comp)

@pytest.fixture
def slow_gen():
    '''
    slow generator
    '''
    comp = SlowGenerator('SlowGen')
    return LibraryComponent('SlowGenC', comp)

@pytest.fixture
def ac_single_back():
    '''
    ac single backup
    '''
    comp = ACSingleBackup('ACSingleBack')
    return LibraryComponent('ACSingleBackC', comp)

@pytest.fixture
def ac_2_back():
    '''
    ac 2way backup
    '''
    comp = AC2WayBackup('AC2Back')
    return LibraryComponent('AC2BackC', comp)

@pytest.fixture
def ac_4_back():
    '''
    ac 4 way backup
    '''
    comp = AC4WayBackup('AC4Back')
    return LibraryComponent('AC4BackC', comp)

@pytest.fixture
def ac_load():
    '''
    AC load
    '''
    comp = OneSideACLoad('ACload')
    return LibraryComponent('ACLoadC', comp)

@pytest.fixture
def dc_tie():
    '''
    DC tie
    '''
    comp = DCTwoSideTie('DC2Tie')
    return LibraryComponent('DC2TieC', comp)

@pytest.fixture
def dc_load():
    '''
    dc load
    '''
    comp = DCLoadContactor('DCLoad')
    return LibraryComponent('DCLoadC', comp)

@pytest.fixture
def gen_lib(abstr_gen, dumb_gen, std_gen, slow_gen):
    '''
    returns a populated library with only the AC generators
    '''
    library = ContractLibrary('gen_lib')

    library.add(abstr_gen)
    library.add(dumb_gen)
    library.add(std_gen)
    library.add(slow_gen)

    #add refinement assertion
    mapping1 = LibraryPortMapping([abstr_gen, dumb_gen])
    mapping1.add(abstr_gen.fail, dumb_gen.fail)
    mapping1.add(abstr_gen.c, dumb_gen.c)

    dumb_gen.add_refinement_assertion(abstr_gen, mapping1)
    #comp_ab.add_refinement_assertion(comp_meta, mapping)

    mapping2 = LibraryPortMapping([abstr_gen, std_gen])
    mapping2.add(abstr_gen.fail, std_gen.fail)
    mapping2.add(abstr_gen.c, std_gen.c)

    std_gen.add_refinement_assertion(abstr_gen, mapping2)

    mapping3 = LibraryPortMapping([abstr_gen, slow_gen])
    mapping3.add(abstr_gen.fail, slow_gen.fail)
    mapping3.add(abstr_gen.c, slow_gen.c)

    slow_gen.add_refinement_assertion(abstr_gen, mapping3)


    library.verify_library()

    #add type compatibilities
    library.add_type(GeneratorT)
    library.add_type(ACContactorT)

    library.add_type_compatibility(GeneratorT, ACContactorT)

    return library

def test_synth_2gen_2c(gen_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1('G1')
    spec2 = GenIsolation2('G2')

    interface = SynthesisInterface([spec1, spec2], gen_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2])

    interface.synthesize()

