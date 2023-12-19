'''
test_spi.py

In this file there is a collection of tests related to the SPI controller
problem.
It uses files from pycox/examples/example_eps
Add reference

Author: Antonio Iannopollo
'''

import pytest
from pyco.examples.example_spi import *


#comps
@pytest.fixture
def counter():
    '''
    counter
    '''
    comp = Counter('Counter')
    return LibraryComponent('Counter', comp)

@pytest.fixture
def comparator():
    '''
    comparator
    '''
    comp = Comparator('Comparator')
    return LibraryComponent('Comparator', comp)

@pytest.fixture
def adc1():
    '''
    adc
    '''
    comp = ADC1('ADC1')
    return LibraryComponent('ADC1', comp)

@pytest.fixture
def adc2():
    '''
    adc
    '''
    comp = ADC2('ADC2')
    return LibraryComponent('ADC2', comp)

@pytest.fixture
def adc2int():
    '''
    adc
    '''
    comp = ADC2int('ADC2int')
    return LibraryComponent('ADC2int', comp)

@pytest.fixture
def adc3():
    '''
    adc
    '''
    comp = ADC3('ADC3')
    return LibraryComponent('ADC3', comp)

@pytest.fixture
def adc3int():
    '''
    adc
    '''
    comp = ADC3int('ADC3int')
    return LibraryComponent('ADC3int', comp)

@pytest.fixture
def adc4int():
    '''
    adc
    '''
    comp = ADC4int('ADC4int')
    return LibraryComponent('ADC4int', comp)

@pytest.fixture
def adc5int():
    '''
    adc
    '''
    comp = ADC5int('ADC5int')
    return LibraryComponent('ADC5int', comp)

@pytest.fixture
def adc6int():
    '''
    adc
    '''
    comp = ADC6int('ADC6int')
    return LibraryComponent('ADC6int', comp)

@pytest.fixture
def adc7int():
    '''
    adc
    '''
    comp = ADC7int('ADC7int')
    return LibraryComponent('ADC7int', comp)

@pytest.fixture
def adc8():
    '''
    adc
    '''
    comp = ADC8('ADC8')
    return LibraryComponent('ADC8', comp)

@pytest.fixture
def adc8int():
    '''
    adc
    '''
    comp = ADC8int('ADC8int')
    return LibraryComponent('ADC8int', comp)


@pytest.fixture
def flipflop():
    '''
    flipflop
    '''
    comp = FlipFlop('ff')
    return LibraryComponent('ff', comp)

@pytest.fixture
def invert():
    '''
    flipflop
    '''
    comp = Invert('invert')
    return LibraryComponent('invert', comp)

@pytest.fixture
def trigger():
    '''
    counter
    '''
    comp = Trigger('Trigger')
    return LibraryComponent('Trigger', comp)

@pytest.fixture
def spi_lib2_int(counter, comparator, adc2int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc2int, number_of_instances=1)
    library.add(flipflop, number_of_instances=2)
    library.add(invert, number_of_instances=2)
    library.add(trigger, number_of_instances=2)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib3_int(counter, comparator, adc3int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc3int, number_of_instances=1)
    library.add(flipflop, number_of_instances=2)
    library.add(invert, number_of_instances=2)
    library.add(trigger, number_of_instances=2)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib4_int(counter, comparator, adc4int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc4int, number_of_instances=1)
    library.add(flipflop, number_of_instances=3)
    library.add(invert, number_of_instances=3)
    library.add(trigger, number_of_instances=3)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib4_int_sd(counter, comparator, adc4int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc4int, number_of_instances=1)
    library.add(flipflop, number_of_instances=3)
    library.add(invert, number_of_instances=3)
    library.add(trigger, number_of_instances=3)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib5_int(counter, comparator, adc5int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc5int, number_of_instances=1)
    library.add(flipflop, number_of_instances=4)
    library.add(invert, number_of_instances=4)
    library.add(trigger, number_of_instances=4)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib5_int_sd(counter, comparator, adc5int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc5int, number_of_instances=1)
    library.add(flipflop, number_of_instances=3)
    library.add(invert, number_of_instances=3)
    library.add(trigger, number_of_instances=3)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library


@pytest.fixture
def spi_lib6_int(counter, comparator, adc6int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc6int, number_of_instances=1)
    library.add(flipflop, number_of_instances=5)
    library.add(invert, number_of_instances=4)
    library.add(trigger, number_of_instances=4)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib6_int_sd(counter, comparator, adc6int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc6int, number_of_instances=1)
    library.add(flipflop, number_of_instances=3)
    library.add(invert, number_of_instances=3)
    library.add(trigger, number_of_instances=3)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib7_int_sd(counter, comparator, adc7int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc7int, number_of_instances=1)
    library.add(flipflop, number_of_instances=3)
    library.add(invert, number_of_instances=3)
    library.add(trigger, number_of_instances=3)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib8_int(counter, comparator, adc8int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=5)
    library.add(comparator, number_of_instances=5)
    library.add(adc8int, number_of_instances=1)
    library.add(flipflop, number_of_instances=7)
    library.add(invert, number_of_instances=8)
    library.add(trigger, number_of_instances=8)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library


@pytest.fixture
def spi_lib8_int_sd(counter, comparator, adc8int, flipflop, invert, trigger):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=2)
    library.add(comparator, number_of_instances=2)
    library.add(adc8int, number_of_instances=1)
    library.add(flipflop, number_of_instances=3)
    library.add(invert, number_of_instances=3)
    library.add(trigger, number_of_instances=3)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)
    library.add_type(DataSignal)

    library.add_type_compatibility(DataSignal, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(ControlSignal, SPICs)
    library.add_type_compatibility(ControlSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    # library.verify_determinism(stop_if_fails=True)
    return library

def test_adc2_int(spi_lib2_int, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec2int('G1')

    interface = SynthesisInterface(spi_lib2_int, [spec])

    adc = interface.get_component('ADC2int')
    interface.use_connected_spec(adc, 'analog', 'analog')

    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False, visualize=visualize)


#uses same library
def test_adc2_int_sd(spi_lib2_int, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec2int('G1')

    interface = SynthesisInterface(spi_lib2_int, [spec])

    adc = interface.get_component('ADC2int')
    interface.use_connected_spec(adc, 'analog', 'analog')

    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True, visualize=visualize)


def test_adc3_int(spi_lib3_int, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec3int('G1')

    interface = SynthesisInterface(spi_lib3_int, [spec])

    adc = interface.get_component('ADC3int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False, visualize=visualize)


def test_adc3_int_sd(spi_lib3_int, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec3int('G1')

    interface = SynthesisInterface(spi_lib3_int, [spec])

    adc = interface.get_component('ADC3int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True, visualize=visualize)


def test_adc4_int(spi_lib4_int, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec4int('G1')

    interface = SynthesisInterface(spi_lib4_int, [spec])

    adc = interface.get_component('ADC4int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False, visualize=visualize)



# def test_adc4_int_sd(spi_lib4_int_sd, visualize):
def test_adc4_int_sd(spi_lib4_int_sd, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec4int('G1')

    interface = SynthesisInterface(spi_lib4_int_sd, [spec])

    adc = interface.get_component('ADC4int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True, visualize=visualize)


def test_adc5_int(spi_lib5_int, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec5int('G1')

    interface = SynthesisInterface(spi_lib5_int, [spec])

    adc = interface.get_component('ADC5int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False, visualize=visualize)

def test_adc5_int_sd(spi_lib5_int_sd, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec5int('G1')

    interface = SynthesisInterface(spi_lib5_int_sd, [spec])

    adc = interface.get_component('ADC5int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True, visualize=visualize)

def test_adc6_int(spi_lib6_int, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec6int('G1')

    interface = SynthesisInterface(spi_lib6_int, [spec])

    adc = interface.get_component('ADC6int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False, visualize=visualize)


def test_adc6_int_sd(spi_lib6_int_sd, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec6int('G1')

    interface = SynthesisInterface(spi_lib6_int_sd, [spec])

    adc = interface.get_component('ADC6int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True, visualize=visualize)

def test_adc8_int(spi_lib8_int, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec8int('G1')

    interface = SynthesisInterface(spi_lib8_int, [spec])

    adc = interface.get_component('ADC8int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False, visualize=visualize)

def test_adc7_int_sd(spi_lib7_int_sd, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec7int('G1')

    interface = SynthesisInterface(spi_lib7_int_sd, [spec])

    adc = interface.get_component('ADC7int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True, visualize=visualize)

def test_adc8_int_sd(spi_lib8_int_sd, visualize):
    '''
    Performs simple synthesis
    '''

    spec = Spec8int('G1')

    interface = SynthesisInterface(spi_lib8_int_sd, [spec])

    adc = interface.get_component('ADC8int')
    interface.use_connected_spec(adc, 'analog', 'analog')
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True, visualize=visualize)
