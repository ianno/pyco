'''
test_edg.py

In this file there is a collection of tests related to the Electronic Device Generation (EDG)
problem.
It uses files from pycox/examples/example_edg
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
def power_adapter12():
    '''
    std generator
    '''
    comp = PowerAdapter12V('Power12')
    return LibraryComponent('Power12', comp)

@pytest.fixture
def GPIO_driver():
    '''
    std generator
    '''
    comp = GPIODriver('GPIODriver')
    return LibraryComponent('GPIODriver', comp)

@pytest.fixture
def LED_driver():
    '''
    std generator
    '''
    comp = LEDDriver('LEDDriver')
    return LibraryComponent('LEDDriver', comp)

@pytest.fixture
def LED_gen():
    '''
    std generator
    '''
    comp = LEDGeneral('LEDGeneral')
    return LibraryComponent('LEDGeneral', comp)

@pytest.fixture
def ACL_driver():
    '''
    std generator
    '''
    comp = AclDriver('AclDriver')
    return LibraryComponent('AclDriver', comp)

@pytest.fixture
def accelerometer():
    '''
    std generator
    '''
    comp = Accelerometer('Accelerometer')
    return LibraryComponent('Accelerometer', comp)

@pytest.fixture
def dcdc3():
    '''
    std generator
    '''
    comp = DcDcConverter12_3('Dcdc3')
    return LibraryComponent('Dcdc3', comp)

@pytest.fixture
def dcdc5():
    '''
    std generator
    '''
    comp = DcDcConverter12_5('Dcdc5')
    return LibraryComponent('Dcdc5', comp)

@pytest.fixture
def simple_MCU():
    '''
    std generator
    '''
    comp = SimpleMCU('SimpleMCU')
    return LibraryComponent('SimpleMCU', comp)

@pytest.fixture
def big_edg_lib(simple_MCU, LED_gen, power_adapter, power_adapter12, dcdc3,
                dcdc5, accelerometer, ACL_driver, LED_driver, GPIO_driver):
    '''
    returns a populated library
    '''
    N = 1
    library = ContractLibrary('big_edg_lib')

    for _ in range(N):
        library.add(simple_MCU)
        library.add(LED_gen)
        library.add(power_adapter)
        library.add(power_adapter12)
        library.add(dcdc3)
        library.add(dcdc5)
        library.add(accelerometer)
        library.add(LED_driver)
        library.add(ACL_driver)
        library.add(GPIO_driver)

    library.verify_library()

    #add type compatibilities
    library.add_type(IOPin)
    library.add_type(Voltage5V)
    library.add_type(VariableVoltage)
    library.add_type(Device)
    library.add_type(LEDDriverT)
    library.add_type(AclDriverT)
    library.add_type(GPIODriverT)
    library.add_type(GND)
    library.add_type(Voltage3V)
    library.add_type(Voltage12V)

    return library


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


def test_big_lib_led(big_edg_lib):
    '''
    Performs simple synthesis
    '''

    # spec1 = SimpleEmpty('Void')

    interface = SynthesisInterface(big_edg_lib)

    led = interface.get_component('LEDGeneral')
    interface.use_component(led)


    interface.synthesize(limit=10)