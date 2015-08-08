'''
test_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
It uses files from pycox/examples/example_eps
Add reference

Author: Antonio Iannopollo
'''


import pytest
from pycox.examples.example_eps_excape import *

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
    lib_c = LibraryComponent('AC2BackC', comp)

    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2])

    return lib_c

@pytest.fixture
def ac_4_back():
    '''
    ac 4 way backup
    '''
    comp = AC4WayBackup('AC4Back')
    lib_c = LibraryComponent('AC4BackC', comp)
    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2,
                                         comp.fail3, comp.fail4])

    return lib_c

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
    lib_c = LibraryComponent('DC2TieC', comp)
    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2])

    return lib_c

@pytest.fixture
def dc_load():
    '''
    dc load
    '''
    comp = DCLoadContactor('DCLoad')
    lib_c = LibraryComponent('DCLoadC', comp)
    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2])

    return lib_c



@pytest.fixture
def ac_lib(abstr_gen, dumb_gen, std_gen, slow_gen, ac_single_back, ac_2_back,
           ac_4_back, ac_load):
    '''
    returns a populated library with only the AC generators
    '''
    library = ContractLibrary('gen_lib')

    library.add(abstr_gen)
    library.add(dumb_gen)
    library.add(std_gen)
    library.add(slow_gen)
    library.add(ac_single_back)
    library.add(ac_2_back)
    library.add(ac_4_back)
    library.add(ac_load)

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
    library.add_type(ACGenContactorT)
    library.add_type(ACBackContactorT)

    library.add_type_compatibility(GeneratorT, ACGenContactorT)

    return library

@pytest.fixture
def acdc_lib(ac_lib, dc_tie, dc_load):
    '''
    extended library
    '''

    ac_lib.add(dc_load)
    ac_lib.add(dc_tie)

    ac_lib.verify_library()

    return ac_lib

def test_synth_2gen_2c_1(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1('G1')
    #spec2 = GenIsolation2('G2')

    interface = SynthesisInterface([spec1], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2])

    interface.synthesize()

def test_synth_2gen_2c_2(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1('G1')
    spec2 = GenIsolation2('G2')

    interface = SynthesisInterface([spec1, spec2], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2])

    interface.synthesize()


def test_synth_4gen_6c_ac_1spec(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')

    interface = SynthesisInterface([spec1], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize()

def test_synth_4gen_6c_ac_2spec(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')

    interface = SynthesisInterface([spec1, spec2], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize()

def test_synth_4gen_6c_ac_3spec(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')

    interface = SynthesisInterface([spec1, spec2, spec3], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize()

def test_synth_4gen_6c_ac_4spec(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')
    spec4 = GenIsolation4B('G4')

    interface = SynthesisInterface([spec1, spec2, spec3, spec4], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize()

def test_synth_4gen_6c_ac_5spec(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')
    spec4 = GenIsolation4B('G4')
    spec5 = NoShort('G5')

    interface = SynthesisInterface([spec1, spec2, spec3, spec4,
                                    spec5], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize()

def test_synth_4gen_6c_ac_6spec(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')
    spec4 = GenIsolation4B('G4')
    spec5 = NoShort('G5')
    spec6 = NoParallelShort('G6')

    interface = SynthesisInterface([spec1, spec2, spec3, spec4,
                                    spec5, spec6], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize()

def test_synth_4gen_6c_ac_7spec(ac_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')
    spec4 = GenIsolation4B('G4')
    spec5 = NoShort('G5')
    spec6 = NoParallelShort('G6')
    spec7 = IsolateEmergencyBus('G7')

    interface = SynthesisInterface([spec1, spec2, spec3, spec4,
                                    spec5, spec6, spec7], ac_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize()

def test_synth_6_10_dc_9spec(acdc_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1D('G1')
    spec2 = GenIsolation2D('G2')
    spec3 = GenIsolation3D('G3')
    spec4 = GenIsolation4D('G4')
    spec5 = NoShortD('G5')
    spec6 = NoParallelShortD('G6')
    spec7 = IsolateEmergencyBusD('G7')
    spec8 = DCRightD('G8')
    spec9 = DCLeftD('G9')

    interface = SynthesisInterface([spec1, spec2, spec3, spec4,
                                    spec5, spec6, spec7, spec8,
                                    spec9], acdc_lib)

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          spec1.fail_r1, spec1.fail_r2])

    interface.synthesize()
