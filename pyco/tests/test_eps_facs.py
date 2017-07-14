'''
test_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
It uses files from pycox/examples/example_eps
Add reference

Author: Antonio Iannopollo
'''


import pytest
from pyco.examples.example_eps_facs import *
from pyco.contract import CompositionMapping

REP = 1

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
def ac_4_back_alt():
    '''
    ac 4 way backup
    '''
    comp = AC4WayBackupAlt('AC4BackAlt')
    lib_c = LibraryComponent('AC4BackAltC', comp)
    lib_c.add_distinct_port_constraints([comp.fail1, comp.fail2,
                                         comp.fail3, comp.fail4])

    return lib_c

@pytest.fixture
def back_gen():
    '''
    back generator
    '''
    comp = ACBackupGen('ACBackupGen')
    return LibraryComponent('ACBackupGen', comp)

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
           ac_4_back, ac_4_back_alt, back_gen, ac_load):
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
    #library.add(ac_4_back_alt)
    #library.add(back_gen)
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

def test_synth_1gen_1c_2(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation0('G1')

    interface = SynthesisInterface(ac_lib, [spec1])

    interface.same_block_constraint([spec1.fail1, spec1.c1])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_2gen_2c_1(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1('G1')
    #spec2 = GenIsolation2('G2')

    interface = SynthesisInterface(ac_lib, [spec1])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_2gen_2c_2(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1('G1')
    spec2 = GenIsolation2('G2')

    interface = SynthesisInterface(ac_lib, [spec1, spec2])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)


def test_synth_2gen_4c_6(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1_6('G1')

    interface = SynthesisInterface(ac_lib, [spec1])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)


def test_synth_2gen_4c_6(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1_6('G1')

    interface = SynthesisInterface(ac_lib, [spec1])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_4gen_6c_ac_1spec(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')

    interface = SynthesisInterface(ac_lib, [spec1])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_4gen_6c_ac_2spec(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')

    interface = SynthesisInterface(ac_lib, [spec1, spec2])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_4gen_6c_ac_3spec(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')

    interface = SynthesisInterface(ac_lib, [spec1, spec2, spec3])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_4gen_6c_ac_4spec(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')
    spec4 = GenIsolation4B('G4')

    interface = SynthesisInterface(ac_lib, [spec1, spec2, spec3, spec4])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_4gen_6c_ac_5spec(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')
    spec4 = GenIsolation4B('G4')
    spec5 = NoShort('G5')

    interface = SynthesisInterface(ac_lib, [spec1, spec2, spec3, spec4,
                                    spec5])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_4gen_6c_ac_6spec(ac_lib, library_redundancy):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1B('G1')
    spec2 = GenIsolation2B('G2')
    spec3 = GenIsolation3B('G3')
    spec4 = GenIsolation4B('G4')
    spec5 = NoShort('G5')
    spec6 = NoParallelShort('G6')

    interface = SynthesisInterface(ac_lib, [spec1, spec2, spec3, spec4,
                                    spec5, spec6])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)

def test_synth_4gen_6c_ac_7spec(ac_lib, library_redundancy):
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

    interface = SynthesisInterface(ac_lib, [spec1, spec2, spec3, spec4,
                                    spec5, spec6, spec7])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])

    interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy)


def test_synth_6_10_dc_1spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1D('G1')

    interface = SynthesisInterface(acdc_lib, [spec1])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])


    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                             library_max_redundancy=library_redundancy,
                             minimize_components=min_comps,
                             minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)


def test_synth_6_10_dc_2spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1D('G1')
    spec2 = GenIsolation2D('G2')

    interface = SynthesisInterface(acdc_lib, [spec1, spec2])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])


    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                             library_max_redundancy=library_redundancy,
                             minimize_components=min_comps,
                             minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)


def test_synth_6_10_dc_3spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1D('G1')
    spec2 = GenIsolation2D('G2')
    spec3 = GenIsolation3D('G3')

    interface = SynthesisInterface(acdc_lib, [spec1, spec2, spec3])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])


    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy,
                         minimize_components=min_comps,
                         minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)


def test_synth_6_10_dc_4spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1D('G1')
    spec2 = GenIsolation2D('G2')
    spec3 = GenIsolation3D('G3')
    spec4 = GenIsolation4D('G4')

    interface = SynthesisInterface(acdc_lib, [spec1, spec2, spec3, spec4])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])


    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy,
                         minimize_components=min_comps,
                         minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)


def test_synth_6_10_dc_5spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1D('G1')
    spec2 = GenIsolation2D('G2')
    spec3 = GenIsolation3D('G3')
    spec4 = GenIsolation4D('G4')
    spec5 = NoShortD('G5')

    interface = SynthesisInterface(acdc_lib, [spec1, spec2, spec3, spec4,
                                    spec5])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])


    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy,
                         minimize_components=min_comps,
                         minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)


def test_synth_6_10_dc_6spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
    '''
    Performs simple synthesis
    '''

    spec1 = GenIsolation1D('G1')
    spec2 = GenIsolation2D('G2')
    spec3 = GenIsolation3D('G3')
    spec4 = GenIsolation4D('G4')
    spec5 = NoShortD('G5')
    spec6 = NoParallelShortD('G6')

    interface = SynthesisInterface(acdc_lib, [spec1, spec2, spec3, spec4,
                                    spec5, spec6])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])


    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy,
                         minimize_components=min_comps,
                         minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)

def test_synth_6_10_dc_7spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
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

    interface = SynthesisInterface(acdc_lib, [spec1, spec2, spec3, spec4,
                                    spec5, spec6, spec7])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])

    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy,
                         minimize_components=min_comps,
                         minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)

def test_synth_6_10_dc_8spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
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

    interface = SynthesisInterface(acdc_lib, [spec1, spec2, spec3, spec4,
                                    spec5, spec6, spec7, spec8])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])

    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy,
                         minimize_components=min_comps,
                         minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)

def test_synth_6_10_dc_9spec(acdc_lib, min_comps, min_ports, library_redundancy, filename):
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

    interface = SynthesisInterface(acdc_lib, [spec1, spec2, spec3, spec4,
                                    spec5, spec6, spec7, spec8,
                                    spec9])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          # spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])

    for _ in range(0, REP):
        interface.synthesize(strict_out_lib_map=False,
                         library_max_redundancy=library_redundancy,
                         minimize_components=min_comps,
                         minimize_ports=min_ports,
                             filename=filename,
                             visualize=False)


############# INCREMENTAL TESTS #################
def test_synth_inc_1(acdc_lib, library_redundancy, no_types, filename):
    '''
    Performs simple synthesis
    1gen 1 c
    '''

    spec1 = GenIsolation0('G1')

    interface = SynthesisInterface(acdc_lib, [spec1])
    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.distinct_ports_constraints([spec1.fail1,
                                          spec1.c1])

    interface.synthesize(strict_out_lib_map=False,
                         use_types=not no_types,
                         use_hints=not no_types,
                         library_max_redundancy=library_redundancy,
                             filename=filename,
                             visualize=False)

def test_synth_inc_2(acdc_lib, library_redundancy, no_types, filename):
    '''
    Performs simple synthesis
    2gen 2 c
    '''

    spec1 = GenIsolation1('G1')

    interface = SynthesisInterface(acdc_lib, [spec1])
    interface.same_block_constraint([spec1.fail1, spec1.c1])


    interface.synthesize(strict_out_lib_map=False,
                         use_types=not no_types,
                         use_hints=not no_types,
                         library_max_redundancy=library_redundancy,
                             filename=filename,
                             visualize=False)

def test_synth_inc_3(acdc_lib, library_redundancy, no_types, filename):
    '''
    Performs simple synthesis
    2gen 4 c
    '''

    spec1 = GenIsolation1_6('G1')

    interface = SynthesisInterface(acdc_lib, [spec1])
    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4])


    interface.synthesize(strict_out_lib_map=False,
                         use_types=not no_types,
                         use_hints=not no_types,
                         library_max_redundancy=library_redundancy,
                             filename=filename,
                             visualize=False)

def test_synth_inc_4(acdc_lib, library_redundancy, no_types, filename):
    '''
    Performs simple synthesis
    4gen 6 c
    '''

    spec1 = GenIsolation1B('G1')

    interface = SynthesisInterface(acdc_lib, [spec1])
    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6])


    interface.synthesize(strict_out_lib_map=False,
                         use_types=not no_types,
                         use_hints=not no_types,
                         library_max_redundancy=library_redundancy,
                             filename=filename,
                             visualize=False)

def test_synth_inc_5(acdc_lib, library_redundancy, no_types, filename):
    '''
    Performs simple synthesis
    6gen 10 c
    '''

    spec1 = GenIsolation1D('G1')

    interface = SynthesisInterface(acdc_lib, [spec1])

    interface.same_block_constraint([spec1.fail1, spec1.c1])
    interface.same_block_constraint([spec1.fail2, spec1.c2])
    interface.same_block_constraint([spec1.fail3, spec1.c3])
    interface.same_block_constraint([spec1.fail4, spec1.c4])
    interface.distinct_ports_constraints([spec1.fail1, spec1.fail2, spec1.fail3, spec1.fail4,
                                          spec1.c1, spec1.c2, spec1.c3,
                                          spec1.c4, spec1.c5, spec1.c6,
                                          spec1.c7, spec1.c8, spec1.c9, spec1.c10,
                                          spec1.fail_r1, spec1.fail_r2])

    interface.synthesize(strict_out_lib_map=False,
                         use_types=not no_types,
                         use_hints=not no_types,
                         library_max_redundancy=library_redundancy,
                             filename=filename,
                             visualize=False)



def test_manual_6_10_dc_9spec(acdc_lib):
    '''
    Performs simple synthesis
    '''

    spec11 = GenIsolation1D('G1')
    spec2 = GenIsolation2D('G2')
    spec3 = GenIsolation3D('G3')
    spec4 = GenIsolation4D('G4')
    spec5 = NoShortD('G5')
    spec6 = NoParallelShortD('G6')
    spec7 = IsolateEmergencyBusD('G7')
    spec8 = DCRightD('G8')
    spec1 = DCLeftD('G9')

    gl = StdGenerator('gl')
    gr = StdGenerator('gr')
    gtie = AC4WayBackup('gtie')
    ll = DCLoadContactor('ll')
    lr = DCLoadContactor('rl')
    ltie = DCTwoSideTie('ltie')

    contracts = [gr, gtie, ll, lr, ltie]
    mapping = CompositionMapping([gl] + contracts)
    mapping.connect(gtie.fail1, gl.fail)
    mapping.connect(gtie.fail4, gr.fail)
    mapping.connect(ltie.fail1, ll.fail1)
    mapping.connect(ltie.fail2, lr.fail2)
    mapping.connect(ll.fail2, lr.fail2)
    mapping.connect(lr.fail1, ll.fail1)

    mapping.add(gl.c, 'cs1')
    mapping.add(gtie.fail2, 'gt_fail2')
    mapping.add(gtie.fail3, 'gt_fail3')
    #mapping.add(gr.c, 'cs4')
    #mapping.add(ll.fail1, 'lfail1')
    #mapping.add(lr.fail1, 'lfail2')
    #mapping.add(gr.c, 'cs4')
    #mapping.add(gr.c, 'cs4')
    #mapping.add(gr.c, 'cs4')
    mapping.add(ll.c, 'c_dcl')
    #gtie.connect_to_port(gtie.fail1, gl.fail)
    #gtie.connect_to_port(gtie.fail4, gr.fail)
    #ltie.connect_to_port(ltie.fail1, ll.p_fail1)
    #ltie.connect_to_port(ltie.fail2, lr.p_fail2)

    spec1.connect_to_port(spec1.fail1, gl.fail)
    spec1.connect_to_port(spec1.fail4, gr.fail)
    spec1.connect_to_port(spec1.fail2, gtie.fail2)
    spec1.connect_to_port(spec1.fail3, gtie.fail3)
    spec1.connect_to_port(spec1.fail_r1, ll.fail1)
    spec1.connect_to_port(spec1.fail_r2, lr.fail2)

    spec1.connect_to_port(spec1.c1, gl.c)
    spec1.connect_to_port(spec1.c4, gr.c)
    spec1.connect_to_port(spec1.c2, gtie.c2)
    spec1.connect_to_port(spec1.c3, gtie.c3)
    spec1.connect_to_port(spec1.c5, gtie.c1)
    spec1.connect_to_port(spec1.c6, gtie.c2)
    spec1.connect_to_port(spec1.c7, ltie.c1)
    spec1.connect_to_port(spec1.c8, ltie.c2)
    spec1.connect_to_port(spec1.c9, ll.c)
    spec1.connect_to_port(spec1.c10, lr.c)


    comp = gl.compose([gr, gtie, ll, lr, ltie], composition_mapping=mapping)

    assert comp.is_refinement(spec1)
