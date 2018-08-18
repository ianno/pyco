'''
example_spi.py

In this file there is a collection of tests related to the SPI controller problem.
Add reference

# TODO: syntax: X4 instead of XXXX
# TODO: arrays bit to bit much
# TODO: basic support of loops (e.g., mach bit in vector to output value on time)

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
    # todo: we could possibly add an assumption which forces the analog signal not to change for N steps after req.
    #       At the same time, the guaranteee will only include one time step comparison with adc line.
    '''
    INPUT_PORTS = [('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit),
                   ('req', Req), ('clk', Clk),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine), ('adcbit_1', AdcBusLine),
                    ('ready', Ready)]
    ASSUMPTIONS = '''!req & G(req -> (X !req & X2 !req & X3 !req & X4 !req))'''
    GUARANTEES = '''G(req -> X4 ready) &
                    G(req -> (
                              ( ((X4 adcbit_0) <-> anbit_0) & ((X4 adcbit_1) <-> anbit_1) ) |
                              ( ((X4 adcbit_0) <-> X anbit_0) & ((X4 adcbit_1) <-> X anbit_1) ) |
                              ( ((X4 adcbit_0) <-> X2 anbit_0) & ((X4 adcbit_1) <-> X2 anbit_1) ) |
                              ( ((X4 adcbit_0) <-> X3 anbit_0) & ((X4 adcbit_1) <-> X3 anbit_1) ) 
                             )
                     )
                    '''

class Spec1bit(Contract):
    '''
    1 bit ADC
    #todo: fix XX and parenthesis
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

#counter block
class SpecCounter(Contract):
    '''
    1 bit ADC
    '''
    INPUT_PORTS = [('reset', Signal), ('clk', Clk),]
    OUTPUT_PORTS = [('outVal', IntegerSignal) ]
    ASSUMPTIONS = ''' G(!reset)'''
    GUARANTEES = '''(  (outVal = 0) & X6 (outVal = 6)  )
                    '''

#counter block
class SpecIncremental(Contract):
    '''
    incremental spec
    '''
    INPUT_PORTS = [('reset', Signal), ('clk', Clk), ]
    OUTPUT_PORTS = [('adcbit_0', Signal),
                    ('ready', Signal)]
    ASSUMPTIONS = '''reset & G(reset -> (X !reset & XX !reset & XXX !reset & XXXX !reset & XXXXX !reset))'''
    GUARANTEES = '''G(reset ->  !ready & X!ready & XXXXready )
                    '''


#2bits library

class Counter(Contract):
    '''
    N Counter
    '''
    INPUT_PORTS = [('reset', Signal), ('clk', Clk), ]
    OUTPUT_PORTS = [('value', IntegerSignal), ('n', IntegerParameter),]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''value = 0 &
                    G(reset -> X (value = 0)) &
                    G((value < n) & !reset -> (X (value) = value + 1)) & 
                    G((value >= n) -> (X (value = 0)))
                    '''

class Counter1(Contract):
    '''
    1- Counter
    '''
    INPUT_PORTS = [('reset', Signal), ('clk', Clk), ]
    OUTPUT_PORTS = [('value', IntegerSignal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''value = 0 &
                    G(reset -> X (value = 0)) &
                    G((value < 1) & !reset -> (X (value) = value + 1)) & 
                    G((value = 1) -> (X (value = 0)))
                    '''

class Counter3(Contract):
    '''
    3- Counter
    '''
    INPUT_PORTS = [('reset', Signal), ('clk', Clk), ]
    OUTPUT_PORTS = [('value', IntegerSignal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''value = 0 &
                    G(reset -> X (value = 0)) &
                    G((value < 1) & !reset -> (X (value) = value + 1)) & 
                    G((value = 1) -> (X (value = 0)))
                    '''

class CounterPiece3(Contract):
    '''
    3- Counter
    '''
    INPUT_PORTS = [ ('clk', Clk), ('acc', IntegerSignal)]
    OUTPUT_PORTS = [('value', IntegerSignal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''value = 3 &
                    G((value < 3)  -> (X (value = acc))) & 
                    G((value = 3) -> (X (value = 0)))
                    '''

class Accumulator(Contract):
    '''
    3- Counter
    '''
    INPUT_PORTS = [('clk', Clk), ('inVal', IntegerSignal)]
    OUTPUT_PORTS = [('outVal', IntegerSignal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''outVal = 1 & G(X(outVal = (inVal + 1)))
                    '''

class Comparator(Contract):
    '''
    N-based comparator
    '''
    INPUT_PORTS = [('val_in', IntegerSignal), ('clk', Clk)]
    OUTPUT_PORTS = [('is_eq', Signal), ('n', IntegerParameter)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !is_eq & 
                     G((val_in = n) -> X is_eq) &
                     G(!(val_in = n) -> X is_eq)
                    '''
class Comparator3(Contract):
    '''
    3-based comparator
    '''
    INPUT_PORTS = [('val_in', IntegerSignal), ('clk', Clk)]
    OUTPUT_PORTS = [('is_eq', Signal),]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !is_eq & G((val_in = 1) -> X is_eq) &
                     G(!(val_in = 1) -> X !is_eq)
                    '''

class Invert(Contract):
    '''
    invert
    '''
    INPUT_PORTS = [('in', Signal),]
    OUTPUT_PORTS = [('out', Signal),]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' G(out = !in)'''
    # GUARANTEES = ''' out = !in'''

class FlipFlop(Contract):
    '''
    a flipflop
    '''
    INPUT_PORTS = [('d', Signal), ('clk', Clk), ('en', Signal)]
    OUTPUT_PORTS = [('q', FlipFlopOut)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !q &
                     G(en & d -> X q) &
                     G(en & !d -> X !q) &
                     G(!en & q -> X q) &
                     G(!en & !q -> X !q)
                    '''

class ADC2(Contract):
    '''
    an AD converter
    '''
    INPUT_PORTS = [('cs', SPICs), ('clk', SPIClk), ('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit)]
    OUTPUT_PORTS = [('miso', SPIMiso)]
    ASSUMPTIONS = '''G(cs -> (X cs & XX cs & XXX cs & XXXX !cs))'''
    GUARANTEES = ''' G(!cs & X cs -> (X anbit_0 <-> XX miso)) &
                     G(!cs & X cs -> (X anbit_1 <-> XXX miso)) 
                    '''

class ADC1(Contract):
    '''
    an 1bit AD converter
    '''
    INPUT_PORTS = [('cs', Signal), ('clk', SPIClk), ('anbit_0', AnalogDataBit)]
    OUTPUT_PORTS = [('miso', SPIMiso)]
    ASSUMPTIONS = '''!cs & G(cs -> (X !cs & XX !cs & XXX !cs & XXXX !cs ))'''
    GUARANTEES = ''' G(!cs & X cs -> (X anbit_0 <-> XXXXX miso))
                    '''