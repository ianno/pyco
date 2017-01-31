'''
test_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
It uses files from pycox/examples/example_eps
Add reference

Author: Antonio Iannopollo
'''


import pytest
from pycox.examples.example_edg import *
from pycox.examples.example_edg import LED as LED_c
from pycox.contract import CompositionMapping


@pytest.fixture
def micro():
    '''
    micro
    '''
    comp = Microcontroller('Micro')
    lib_c = LibraryComponent('Micro', comp)
    lib_c.add_distinct_port_constraints([comp.pwr, comp.io])
    return lib_c

@pytest.fixture
def LED():
    '''
    LED
    '''
    comp = LED_c('LED')
    return LibraryComponent('LED', comp)

@pytest.fixture
def doubleLED():
    '''
    LED
    '''
    comp = DoubleLED('dLED')
    return LibraryComponent('dLED', comp)

@pytest.fixture
def power_adapter():
    '''
    std generator
    '''
    comp = PowerAdapter5V('Power')
    return LibraryComponent('Power', comp)





@pytest.fixture
def edg_lib(micro, LED, doubleLED, power_adapter):
    '''
    returns a populated library
    '''
    library = ContractLibrary('edg_lib')

    library.add(micro)
    library.add(LED)
    library.add(doubleLED)
    library.add(power_adapter)

    library.verify_library()

    #add type compatibilities
    library.add_type(IOPin)
    library.add_type(Voltage)
    library.add_type(Voltage5V)
    library.add_type(VariableVoltage)
    library.add_type(Device)
    library.add_type(LEDDevice)
    library.add_type(GND)
    library.add_type(Voltage5V)

    library.add_type_compatibility(IOPin, Voltage)

    return library


def test_base_oldstyle(edg_lib):
    '''
    Performs simple synthesis
    '''

    spec1 = SimpleLED('LED1')
    #spec2 = GenIsolation2('G2')

    interface = SynthesisInterface(edg_lib, [spec1])

    interface.synthesize(limit=5)


def test_base_empty(edg_lib):
    '''
    Performs simple synthesis
    '''

    interface = SynthesisInterface(edg_lib)

    interface.synthesize(limit=5)

def test_base_use_dled(edg_lib):
    '''
    Performs simple synthesis
    '''

    interface = SynthesisInterface(edg_lib)

    double_led = interface.get_component('dLED')
    interface.use_component(double_led)

    interface.synthesize(limit=5)

def test_base_use_micro(edg_lib):
    '''
    Performs simple synthesis
    '''

    interface = SynthesisInterface(edg_lib)

    micro = interface.get_component('Micro')
    interface.use_component(micro)

    interface.synthesize(limit=5)

def test_base_use_micro_and_led(edg_lib):
    '''
    Performs simple synthesis
    '''

    # spec1 = SimpleEmpty('Void')

    interface = SynthesisInterface(edg_lib)

    micro = interface.get_component('Micro')
    led = interface.get_component('LED')
    interface.use_connected(micro, 'io', led, 'pwr')
    interface.synthesize(limit=5)

def test_base_use_micro_and_2led(edg_lib):
    '''
    Performs simple synthesis
    '''

    # spec1 = SimpleEmpty('Void')

    interface = SynthesisInterface(edg_lib)

    micro = interface.get_component('Micro')
    led = interface.get_component('LED')
    led1 = interface.get_component('LED')
    interface.use_connected(micro, 'io', led, 'pwr')
    interface.use_component(led1, level=1)

    interface.synthesize(limit=5)