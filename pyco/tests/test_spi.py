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
from pyco.contract import CompositionMapping


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
def adc3():
    '''
    adc
    '''
    comp = ADC3('ADC3')
    return LibraryComponent('ADC3', comp)

@pytest.fixture
def adc8():
    '''
    adc
    '''
    comp = ADC8('ADC8')
    return LibraryComponent('ADC8', comp)

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
def accumulator():
    '''
    counter
    '''
    comp = Accumulator('Accumulator')
    return LibraryComponent('Accumulator', comp)

@pytest.fixture
def spi_lib1(counter, comparator, adc1, flipflop, invert, accumulator):
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
    library.add(adc1, number_of_instances=1)
    library.add(flipflop, number_of_instances=2)
    library.add(invert, number_of_instances=2)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)

    library.add_type_compatibility(FlipFlopOut, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)

    library.verify_determinism(stop_if_fails=True)

    return library

@pytest.fixture
def spi_lib2(counter, comparator, adc2, flipflop, invert, trigger, accumulator):
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
    library.add(adc2, number_of_instances=1)
    library.add(flipflop, number_of_instances=2)
    library.add(invert, number_of_instances=2)
    library.add(trigger, number_of_instances=2)
    # library.add(counter_piece, number_of_instances=1)
    # library.add(accumulator, number_of_instances=1)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)

    library.add_type_compatibility(FlipFlopOut, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(DelayedSignal, SPICs)
    library.add_type_compatibility(DelayedSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)


    library.verify_determinism(stop_if_fails=True)
    return library

@pytest.fixture
def spi_lib3(counter, comparator, adc3, flipflop, invert, trigger, accumulator):
    '''
    library
    :param counter:
    :param comparator:
    :param adc:
    :param flipflop:
    :return:
    '''

    library = ContractLibrary('spilib')

    library.add(counter, number_of_instances=3)
    library.add(comparator, number_of_instances=3)
    library.add(adc3, number_of_instances=1)
    library.add(flipflop, number_of_instances=3)
    library.add(invert, number_of_instances=3)
    library.add(trigger, number_of_instances=3)
    # library.add(counter_piece, number_of_instances=1)
    # library.add(accumulator, number_of_instances=1)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)

    library.add_type_compatibility(FlipFlopOut, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(DelayedSignal, SPICs)
    library.add_type_compatibility(DelayedSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)
    library.add_type_compatibility(DelayedSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    library.verify_determinism(stop_if_fails=True)
    return library


@pytest.fixture
def spi_lib8(counter, comparator, adc8, flipflop, invert, trigger, accumulator):
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
    library.add(adc8, number_of_instances=1)
    library.add(flipflop, number_of_instances=2)
    library.add(invert, number_of_instances=2)
    library.add(trigger, number_of_instances=2)
    # library.add(counter_piece, number_of_instances=1)
    # library.add(accumulator, number_of_instances=1)

    # add type compatibilities
    library.add_type(FlipFlopOut)
    library.add_type(FlipFlopIn)
    library.add_type(AdcBusLine)
    library.add_type(SPIMiso)
    library.add_type(DelayedSignal)
    library.add_type(ControlSignal)
    library.add_type(SPICs)
    library.add_type(Ready)

    library.add_type_compatibility(FlipFlopOut, AdcBusLine)
    library.add_type_compatibility(SPIMiso, AdcBusLine)
    library.add_type_compatibility(SPIMiso, FlipFlopIn)
    library.add_type_compatibility(DelayedSignal, SPICs)
    library.add_type_compatibility(DelayedSignal, Ready)
    library.add_type_incompatibility(DelayedSignal, ControlSignal)

    library.verify_determinism(stop_if_fails=True)
    return library


def test_adc1(spi_lib1):
    '''
    Performs simple synthesis
    '''

    spec1 = Spec1bit('G1')
    # spec1 = Spec2bit('G1')
    #spec1 = Spec3bit('G1')
    # spec1 = Spec('G1')
    # spec1 = SpecIncremental('G1')

    interface = SynthesisInterface(spi_lib1, [spec1])

    #adc = interface.get_component('ADC')
    #interface.use_component(adc)
    # interface.use_connected_spec(adc, 'anbit_0', 'anbit_0')


    # interface.synthesize(max_depth=4, library_max_redundancy=1)
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False)

def test_adc2(spi_lib2):
    '''
    Performs simple synthesis
    '''

    spec = Spec2bit('G1')

    interface = SynthesisInterface(spi_lib2, [spec])

    adc = interface.get_component('ADC2')
    # interface.use_component(adc)
    interface.use_connected_spec(adc, 'anbit_0', 'anbit_1')
    interface.use_connected_spec(adc, 'anbit_1', 'anbit_0')

    # interface.synthesize(max_depth=4, library_max_redundancy=1)
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False)

def test_adc3(spi_lib3):
    '''
    Performs simple synthesis
    '''

    spec = Spec3bit('G1')

    interface = SynthesisInterface(spi_lib3, [spec])

    adc = interface.get_component('ADC3')
    # interface.use_component(adc)
    interface.use_connected_spec(adc, 'anbit_0', 'anbit_0')
    interface.use_connected_spec(adc, 'anbit_1', 'anbit_1')
    interface.use_connected_spec(adc, 'anbit_2', 'anbit_2')
    # interface.synthesize(max_depth=4, library_max_redundancy=1)
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=False)

def test_adc3_inc(spi_lib3):
    '''
    Performs simple synthesis
    '''

    spec = Spec3Incr('G1')

    interface = SynthesisInterface(spi_lib3, [spec])

    adc = interface.get_component('ADC3')
    # interface.use_component(adc)
    interface.use_connected_spec(adc, 'anbit_0', 'anbit_0')
    interface.use_connected_spec(adc, 'anbit_1', 'anbit_1')
    interface.use_connected_spec(adc, 'anbit_2', 'anbit_2')
    # interface.synthesize(max_depth=4, library_max_redundancy=1)
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True)


def test_adc8_inc(spi_lib8):
    '''
    Performs simple synthesis
    '''

    spec = Spec8bit('G1')
    #TODO

    interface = SynthesisInterface(spi_lib8, [spec])

    adc = interface.get_component('ADC8')
    # interface.use_component(adc)
    interface.use_connected_spec(adc, 'anbit_0', 'anbit_0')
    interface.use_connected_spec(adc, 'anbit_1', 'anbit_1')
    interface.use_connected_spec(adc, 'anbit_2', 'anbit_2')
    interface.use_connected_spec(adc, 'anbit_3', 'anbit_3')
    interface.use_connected_spec(adc, 'anbit_4', 'anbit_4')
    interface.use_connected_spec(adc, 'anbit_5', 'anbit_5')
    interface.use_connected_spec(adc, 'anbit_6', 'anbit_6')
    interface.use_connected_spec(adc, 'anbit_7', 'anbit_7')
    # interface.synthesize(max_depth=4, library_max_redundancy=1)
    interface.synthesize(max_depth=4, library_max_redundancy=1, decompose=True)