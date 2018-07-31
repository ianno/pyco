'''
example_spi.py

In this file there is a collection of tests related to the SPI controller problem.
Add reference

Author: Antonio Iannopollo, Inigo Incer
'''

from pyco.contract import Contract, BaseTypeBool, BaseTypeInt, ParameterInt
from pyco.library import (ContractLibrary, LibraryComponent,
                          LibraryPortMapping, LibraryCompositionMapping)
from pyco.synthesis import SynthesisInterface
from pyco import LOG


#let's start with types
class IntegerParameter(ParameterInt):
    '''
    just an integer parameter
    '''
    pass

class IntegerSignal(BaseTypeInt):
    '''
    just an integer parameter
    '''
    pass

class Signal(BaseTypeBool):
    '''
    a logic signal
    '''
    pass

class Clk(Signal):
    '''
    clock signal
    '''
    pass

class Req(Signal):
    '''
    Request signal
    '''
    pass

class Ready(Signal):
    '''
    Ready signal
    '''
    pass


class BusLine(Signal):
    '''
    Bus Line
    '''
    pass

class AdcBusLine(BusLine):
    '''
    ADC Bus line
    '''
    pass

class SPIClk(Clk):
    '''
    SPI clock
    '''
    pass

class SPICs(Signal):
    '''
    SPI chip select
    '''
    pass

class SPIMiso(Signal):
    '''
    SPI Master In Slave Out
    '''

class AnalogDataBit(Signal):
    '''
    Analog Data bit
    '''

class FlipFlopOut(Signal):
    '''
    FlipFlop output
    '''


#first spec
class Spec(Contract):
    '''
    2 bits ADC
    '''
    INPUT_PORTS = [('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit),
                   ('req', Req), ('clk', Clk),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine), ('adcbit_1', AdcBusLine),
                    ('ready', Ready)]
    ASSUMPTIONS = '''!req & G(req -> (X !req & XX !req & XXX !req & XXXX !req))'''
    GUARANTEES = '''G(req -> XXXX ready) &
                    G(req -> ((XXXX (adcbit_0 <-> anbit_0) & XXXX (adcbit_1 <-> anbit_1)) |
                              (XXXX (adcbit_0 <-> X anbit_0) & XXXX (adcbit_1 <-> X anbit_1)) |
                              (XXXX (adcbit_0 <-> XX anbit_0) & XXXX (adcbit_1 <-> XX anbit_1)) |
                              (XXXX (adcbit_0 <-> XXX anbit_0) & XXXX (adcbit_1 <-> XXX anbit_1)) 
                             )
                     )
                    '''

class Spec1bit(Contract):
    '''
    1 bit ADC
    '''
    INPUT_PORTS = [('anbit_0', AnalogDataBit),
                   ('req', Req), ('clk', Clk),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine),
                    ('ready', Ready)]
    ASSUMPTIONS = '''!req & G(req -> (X !req & XX !req ))'''
    GUARANTEES = '''G(req -> XX ready) &
                    G(req -> ((XX (adcbit_0 <-> anbit_0) ) |
                              (XX (adcbit_0 <-> X anbit_0) ) |
                              (XX (adcbit_0 <-> XX anbit_0) ) |
                              (XX (adcbit_0 <-> XXX anbit_0) ) 
                             )
                     )
                    '''

#2bits library

class Counter(Contract):
    '''
    N-bits Counter
    '''
    INPUT_PORTS = [('reset', Signal), ('clk', Clk), ('n', IntegerParameter),]
    OUTPUT_PORTS = [('value', IntegerSignal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''value = 0 &
                    G(reset -> X (value = 0)) &
                    G((value < n) -> (X (value = value + 1))) & 
                    G((value = n) -> (X (value = 0)))
                    '''

class Comparator(Contract):
    '''
    N-based comparator
    '''
    INPUT_PORTS = [('val_in', IntegerSignal), ('clk', Clk), ('n', IntegerParameter)]
    OUTPUT_PORTS = [('is_eq', Signal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' G((val_in = n) -> is_eq) &
                     G(!(val_in = n) -> !is_eq)
                    '''


class FlipFlop(Contract):
    '''
    a flipflop
    '''
    INPUT_PORTS = [('val_in', Signal), ('clk', Clk), ('rec', Signal)]
    OUTPUT_PORTS = [('val_out', FlipFlopOut)]
    ASSUMPTIONS = '''G(rec -> X!rec)'''
    GUARANTEES = ''' !val_out &
                     G(rec & val_in -> X val_out) &
                     G(rec & !val_in -> X !val_out) &
                     G(!rec & val_out -> X val_out) &
                     G(!rec & !val_out -> X !val_out)
                    '''

class ADC2(Contract):
    '''
    an AD converter
    '''
    INPUT_PORTS = [('cs', SPICs), ('clk', SPIClk), ('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit)]
    OUTPUT_PORTS = [('miso', SPIMiso)]
    ASSUMPTIONS = '''G(cs -> (X cs & XX cs & XXX cs & XXXX !cs))'''
    GUARANTEES = ''' G(!cs & X cs & X anbit_0 -> X miso) &
                     G(!cs & X cs & X !anbit_0 -> X !miso) &
                     G(!cs & X cs & X anbit_1 -> XX miso) &
                     G(!cs & X cs & X !anbit_1 -> XX !miso)
                    '''

class ADC1(Contract):
    '''
    an 1bit AD converter
    '''
    INPUT_PORTS = [('cs', SPICs), ('clk', SPIClk), ('anbit_0', AnalogDataBit)]
    OUTPUT_PORTS = [('miso', SPIMiso)]
    ASSUMPTIONS = '''G(cs -> (X cs & XX !cs))'''
    GUARANTEES = ''' G(!cs & X cs & X anbit_0 -> X miso) &
                     G(!cs & X cs & X !anbit_0 -> X !miso) 
                    '''