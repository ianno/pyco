'''
In this file there is a collection of tests related to the Electronic Device Generation (EDG)
problem.
It uses files from pycox/examples/example_edg
Add reference
'''


import pytest
from pycox.examples.example_edg_motor import *


@pytest.fixture
def simple_mcu():
    '''
    micro
    '''
    comp = SimpleMCU('simple_MCU')
    lib_c = LibraryComponent('simple_MCU', comp)
    return lib_c

@pytest.fixture
def small_mcu():
    '''
    micro
    '''
    comp = SmallMCU('small_MCU')
    lib_c = LibraryComponent('small_MCU', comp)
    return lib_c

@pytest.fixture
def mcu():
    '''
    micro
    '''
    comp = MCU('MCU')
    lib_c = LibraryComponent('MCU', comp)
    return lib_c

@pytest.fixture
def dcdc3():
    '''
    LED
    '''
    comp = DcDcConverter12_3('dcdc3')
    return LibraryComponent('dcdc3', comp)

@pytest.fixture
def dcdc5():
    '''
    LED
    '''
    comp = DcDcConverter12_5('dcdc5')
    return LibraryComponent('dcdc5', comp)

@pytest.fixture
def power_generator12():
    '''
    std generator
    '''
    comp = PowerAdapter12V('Power12')
    return LibraryComponent('Power12', comp)

@pytest.fixture
def power_generator5():
    '''
    std generator
    '''
    comp = PowerAdapter5V('Power5')
    return LibraryComponent('Power5', comp)

@pytest.fixture
def half_bridge0():
    '''
    std generator
    '''
    comp = HalfBridge('half_bridge0')
    hbridge = LibraryComponent('half_bridge0', comp)
    hbridge.add_distinct_port_constraints([comp.vin, comp.o1])
    return hbridge

@pytest.fixture
def half_bridge1():
    '''
    std generator
    '''
    comp = HalfBridge('half_bridge1')
    hbridge = LibraryComponent('half_bridge1', comp)
    hbridge.add_distinct_port_constraints([comp.vin, comp.o1])
    return hbridge

@pytest.fixture
def half_bridge2():
    '''
    std generator
    '''
    comp = HalfBridge('half_bridge2')
    hbridge = LibraryComponent('half_bridge2', comp)
    hbridge.add_distinct_port_constraints([comp.vin, comp.o1])
    return hbridge

@pytest.fixture
def edg_mlib(simple_mcu, small_mcu,  mcu, dcdc3, dcdc5, power_generator12, power_generator5,
             half_bridge0, half_bridge1, half_bridge2):

    '''
    returns a populated library
    '''
    library = ContractLibrary('edg_motor_lib')

    library.add(simple_mcu)
    # library.add(small_mcu)
    library.add(mcu)
    library.add(dcdc3)
    library.add(dcdc5)
    library.add(power_generator5)
    library.add(power_generator12)
    library.add(half_bridge0)
    library.add(half_bridge1)
    library.add(half_bridge2)

    library.verify_library()

    #add type compatibilities
    library.add_type(IOPin3)
    library.add_type(IOPin12)
    library.add_type(Voltage)
    library.add_type(Voltage5V)
    library.add_type(Voltage3V)
    library.add_type(Voltage12V)
    library.add_type(GND)


    return library


@pytest.fixture
def edg_mlib_easy(simple_mcu, small_mcu,  mcu, dcdc3, dcdc5, power_generator12, power_generator5,
             half_bridge0, half_bridge1, half_bridge2):

    '''
    returns a populated library
    '''
    library = ContractLibrary('edg_motor_lib')

    #library.add(simple_mcu)
    library.add(small_mcu)
    #library.add(mcu)
    library.add(dcdc3)
    #library.add(dcdc5)
    #library.add(power_generator5)
    library.add(power_generator12)
    library.add(half_bridge0)
    library.add(half_bridge1)
    library.add(half_bridge2)

    library.verify_library()

    #add type compatibilities
    library.add_type(IOPin3)
    library.add_type(IOPin12)
    library.add_type(Voltage)
    library.add_type(Voltage5V)
    library.add_type(Voltage3V)
    library.add_type(Voltage12V)
    library.add_type(GND)


    return library


def test_base(edg_mlib):
    '''
    Performs simple synthesis
    '''

    interface = SynthesisInterface(edg_mlib)

    hbridge = interface.get_component('half_bridge0')
    interface.use_component(hbridge)

    interface.synthesize(limit=5)

def test_base_3HB(edg_mlib):
    '''
    Performs simple synthesis
    '''

    interface = SynthesisInterface(edg_mlib)

    hbridge = interface.get_component('half_bridge0')
    interface.use_component(hbridge)
    hbridge = interface.get_component('half_bridge1')
    interface.use_component(hbridge)
    hbridge = interface.get_component('half_bridge2')
    interface.use_component(hbridge)

    interface.synthesize(limit=8)

def test_simple_spec(edg_mlib):
    '''
    Simple test including spec
    :param edg_mlib:
    :return:
    '''

    spec = SimpleReq('R1')
    interface = SynthesisInterface(edg_mlib, [spec])


    interface.synthesize(limit=8)

def test_simple_spec_d(edg_mlib):
    '''
    Simple test including spec
    :param edg_mlib:
    :return:
    '''

    spec = SimpleReq('R1_distinct')
    interface = SynthesisInterface(edg_mlib, [spec])
    interface.distinct_ports_constraints([spec.o1, spec.o2, spec.o3])

    interface.synthesize(limit=8)

def test_ltl_spec_easy(edg_mlib_easy):
    '''
    Simple test including spec
    :param edg_mlib:
    :return:
    '''

    spec = AlternateWaveReq('R_ltl')
    interface = SynthesisInterface(edg_mlib_easy, [spec])
    interface.distinct_ports_constraints([spec.o1, spec.o2, spec.o3])
    mcu = interface.get_component('small_MCU')
    h0 = interface.get_component('half_bridge0')
    h1 = interface.get_component('half_bridge1')
    h2 = interface.get_component('half_bridge2')

    interface.use_connected(mcu, 'o1', h0, 'i1')
    interface.use_connected(mcu, 'o2', h1, 'i1')
    interface.use_connected(mcu, 'o3', h2, 'i1')

    interface.use_connected_spec(h0, 'o1', 'o1')
    interface.use_connected_spec(h1, 'o1', 'o2')
    interface.use_connected_spec(h2, 'o1', 'o3')

    interface.synthesize(limit=8)

def test_ltl_spec_easy2(edg_mlib):
    '''
    Simple test including spec
    :param edg_mlib:
    :return:
    '''

    spec = AlternateWaveReq('R_ltl')
    interface = SynthesisInterface(edg_mlib, [spec])
    interface.distinct_ports_constraints([spec.o1, spec.o2, spec.o3])
    mcu = interface.get_component('small_MCU')
    h0 = interface.get_component('half_bridge0')
    h1 = interface.get_component('half_bridge1')
    h2 = interface.get_component('half_bridge2')

    interface.use_connected(mcu, 'o1', h0, 'i1')
    interface.use_connected(mcu, 'o2', h1, 'i1')
    interface.use_connected(mcu, 'o3', h2, 'i1')


    interface.synthesize(limit=8)

def test_ltl_spec(edg_mlib):
    '''
    Simple test including spec

    01/31/2017:
    simple_mcu:
    37 sec without optimal strategy
    46 sec with optimal

    mcu:
    49 sec with optimal


    ---
    with
    library.add(simple_mcu)
    # library.add(small_mcu)
    library.add(mcu)
    library.add(dcdc3)
    library.add(dcdc5)
    library.add(power_generator5)
    library.add(power_generator12)
    library.add(half_bridge0)
    library.add(half_bridge1)
    library.add(half_bridge2)

    library.verify_library()

    #add type compatibilities
    library.add_type(IOPin3)
    library.add_type(IOPin12)
    library.add_type(Voltage)
    library.add_type(Voltage5V)
    library.add_type(Voltage3V)
    library.add_type(Voltage12V)
    library.add_type(GND)

    15946.16 sec

    :param edg_mlib:
    :return:
    '''

    spec = AlternateWaveReq('R_ltl')
    interface = SynthesisInterface(edg_mlib, [spec])
    interface.distinct_ports_constraints([spec.o1, spec.o2, spec.o3])


    interface.synthesize(limit=8)