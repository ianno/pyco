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

class DigitalSignal(BaseTypeBool):
    '''
    a logic signal
    '''
    pass

class Clk(DigitalSignal):
    '''
    clock signal
    '''
    pass

class ControlSignal(DigitalSignal):
    '''
    Request signal
    '''
    pass

class DelayedSignal(ControlSignal):
    '''
    Request signal
    '''
    pass

class DataSignal(DigitalSignal):
    '''
    Request signal
    '''
    pass

class Req(ControlSignal):
    '''
    Request signal
    '''
    pass

class Ready(ControlSignal):
    '''
    Ready signal
    '''
    pass


class BusLine(DataSignal):
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

class SPICs(DigitalSignal):
    '''
    SPI chip select
    '''
    pass

class SPIMiso(DataSignal):
    '''
    SPI Master In Slave Out
    '''

class AnalogDataBit(Signal):
    '''
    Analog Data bit
    '''

class FlipFlopOut(DataSignal):
    '''
    FlipFlop output
    '''

class FlipFlopIn(DataSignal):
    '''
    FlipFlop output
    '''

class FlipFlopEn(ControlSignal):
    '''
    FlipFlop output
    '''

class InternalCounter(IntegerSignal):
    '''
    FlipFlop output
    '''


class CounterSignal(BaseTypeInt):
    '''
    just an integer parameter
    '''
    pass

#first spec
class Spec(Contract):
    '''
    2 bits ADC
    # todo: we could possibly add an assumption which forces the analog signal not to change for N steps after req.
    #       At the same time, the guaranteee will only include one time step comparison with adc line.
    '''
    INPUT_PORTS = [('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit),
                   ('req', Req),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine), ('adcbit_1', AdcBusLine),
                    ('ready', DigitalSignal)]
    ASSUMPTIONS = '''G(req -> (X !req & X2 !req & X3 !req & X4 !req))'''
    GUARANTEES = '''G(req -> (
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
                   ('req', Req),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine),
                    ('ready', ControlSignal)]
    ASSUMPTIONS = '''!req & G(req -> (X !req & X2 !req & X3 !req & X4 !req   ))'''
    GUARANTEES = '''G(req -> (  X2 !ready & X3 !ready & X4 ready ) )&
                    G(req -> (
                              ( ((X4 adcbit_0) <-> anbit_0))  |
                              ( ((X4 adcbit_0) <-> X anbit_0)  ) |
                              ( ((X4 adcbit_0) <-> X2 anbit_0)  ) |
                              ( ((X4 adcbit_0) <-> X3 anbit_0) ) 
                             )
                     
                     )
                    '''
    # ASSUMPTIONS = '''(req ) & G(req -> (!( X req))) & G(X!req -> X2(!req))'''
    # GUARANTEES = '''G(req -> (X ! ready &  X2 !ready & X3ready ))
    #               & G(req -> (
    #                           ( ((X3 adcbit_0) <-> anbit_0))  |
    #                           ( ((X3 adcbit_0) <-> X anbit_0)  ) |
    #                           ( ((X3 adcbit_0) <-> X2 anbit_0)  )
    #                          )
    #                  )
    #
    #                 '''


class Spec2bit(Contract):
    '''
    1 bit ADC
    '''
    INPUT_PORTS = [('anbit_0', AnalogDataBit),('anbit_1', AnalogDataBit),
                   ('req', Req),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine),
                    ('adcbit_1', AdcBusLine),
                    ('ready', Ready)]
    ASSUMPTIONS = '''!req & G(req -> (X !req & X2 !req & X3 !req & X4 !req   ))'''
    GUARANTEES = '''G(req -> (  X !ready & X2 !ready & X3 !ready & X4 ready  )) &
                    G(req -> (

                              ( ((X4 adcbit_0) <-> X2 anbit_0) & ((X4 adcbit_1) <-> X2 anbit_1) )
                             )

                     )
                     '''
    # GUARANTEES = '''G(req -> (  X2 !ready & X3 !ready & X4 ready )) &
    #                 G(req -> (
    #                           ( ((X4 adcbit_0) <-> anbit_0) & ((X4 adcbit_1) <-> anbit_1) ) |
    #                           ( ((X4 adcbit_0) <-> X anbit_0) & ((X4 adcbit_1) <-> X anbit_1) ) |
    #                           ( ((X4 adcbit_0) <-> X2 anbit_0) & ((X4 adcbit_1) <-> X2 anbit_1) ) |
    #                           ( ((X4 adcbit_0) <-> X3 anbit_0) & ((X4 adcbit_1) <-> X3 anbit_1) )
    #                          )
    #                  )
    #                 '''


class Spec3bit(Contract):
    '''
    1 bit ADC
    '''
    INPUT_PORTS = [('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit),
                   ('anbit_2', AnalogDataBit), ('req', Req),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine),
                    ('adcbit_1', AdcBusLine),
                    ('adcbit_2', AdcBusLine),
                    ('ready', Ready)]
    ASSUMPTIONS = '''!req & G(req -> (X !req & X2 !req & X3 !req & X4 !req & X5 !req   ))'''
    GUARANTEES = '''G(req -> (  X !ready & X2 !ready & X3 !ready & X4 !ready & X5 ready )) &
                    G(req -> (

                              ( ((X5 adcbit_0) <-> X2 anbit_0) & ((X5 adcbit_1) <-> X2 anbit_1) & ((X5 adcbit_2) <-> X2 anbit_2))  
                             )
                     
                     )
                    '''


class Spec8bit(Contract):
    '''
    1 bit ADC
    '''
    INPUT_PORTS = [('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit),
                   ('anbit_2', AnalogDataBit), ('anbit_3', AnalogDataBit),
                   ('anbit_4', AnalogDataBit), ('anbit_5', AnalogDataBit),
                   ('anbit_6', AnalogDataBit), ('anbit_7', AnalogDataBit),
                   ('req', Req),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine), ('adcbit_1', AdcBusLine),
                    ('adcbit_2', AdcBusLine), ('adcbit_3', AdcBusLine),
                    ('adcbit_4', AdcBusLine), ('adcbit_5', AdcBusLine),
                    ('adcbit_6', AdcBusLine), ('adcbit_7', AdcBusLine),
                    ('ready', Ready)]
    ASSUMPTIONS = '''!req & G(req -> (X !req & X2 !req & X3 !req & X4 !req & X5 !req & 
                                      X6 !req & X7 !req & X8 !req & X9 !req & X10 !req ))'''
    GUARANTEES = '''G(req -> (  X !ready & X2 !ready & X3 !ready & X4 !ready & X5 !ready &
                                X6 !ready & X7 !ready & X8 !ready & X9 !ready & X10 ready)) &
                    G(req -> (

                              ( ((X10 adcbit_0) <-> X2 anbit_0) & 
                                ((X10 adcbit_1) <-> X2 anbit_1) & 
                                ((X10 adcbit_2) <-> X2 anbit_2) & 
                                ((X10 adcbit_3) <-> X2 anbit_3) & 
                                ((X10 adcbit_4) <-> X2 anbit_4) & 
                                ((X10 adcbit_5) <-> X2 anbit_5) & 
                                ((X10 adcbit_6) <-> X2 anbit_6) & 
                                ((X10 adcbit_7) <-> X2 anbit_7))  
                             )

                     )
                    '''

#counter block
class SpecCounter(Contract):
    '''
    1 bit ADC
    '''
    INPUT_PORTS = [('reset', DigitalSignal), ]
    OUTPUT_PORTS = [('is_eq', DigitalSignal) ]
    ASSUMPTIONS = ''' GF(reset)'''
    GUARANTEES = '''(!is_eq) & G(is_eq ->  X(!is_eq)& X2(is_eq)  )
                    '''

#counter block
class Spec3Incr(Contract):
    '''
    1 bit ADC
    '''
    INPUT_PORTS = [('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit),
                   ('anbit_2', AnalogDataBit), ('req', Req),
                   ]
    OUTPUT_PORTS = [('adcbit_0', AdcBusLine),
                    ('adcbit_1', AdcBusLine),
                    ('adcbit_2', AdcBusLine),
                    ('ready', Ready)]
    ASSUMPTIONS = '''!req & G(req -> (X !req & X2 !req & X3 !req & X4 !req & X5 !req   ))'''
    GUARANTEES = '''G(req -> (  X !ready & X2 !ready & X3 !ready & X4 !ready & X5 ready ) &
                    G(req -> (
                              ( ((X5 adcbit_0) <-> X2 anbit_0) & ((X5 adcbit_1) <-> X2 anbit_1) & ((X5 adcbit_2) <-> X2 anbit_2))  
                             )
                     )
                     )
                    '''


#2bits library

class Counter(Contract):
    '''
    N Counter
    '''
    INPUT_PORTS = [('reset', ControlSignal),  ]
    OUTPUT_PORTS = [('value', CounterSignal), ('n', IntegerParameter),]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''value = 0 &
                    G(reset -> X (value = 0)) &
                    G((value < n) & !reset -> (X (value) = value + 1)) & 
                    G((value >= n)& !reset -> (X (value = n))) & 
                    G(n>=0 & n<=10)
                    '''



class Counter1(Contract):
    '''
    1- Counter
    '''
    INPUT_PORTS = [('reset', DigitalSignal), ]
    OUTPUT_PORTS = [('value', IntegerSignal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''value = 0 &
                    G(reset -> X (value = 0)) &
                    G((value < 1) & !reset -> (X (value) = value + 1)) & 
                    G((value = 1) & !reset-> (X (value = 0)))
                    '''

class Counter3(Contract):
    '''
    3- Counter
    '''
    INPUT_PORTS = [('reset', DigitalSignal),  ]
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
    INPUT_PORTS = [ ('acc', IntegerSignal)]
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
    INPUT_PORTS = [('inVal', IntegerSignal)]
    OUTPUT_PORTS = [('outVal', IntegerSignal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''outVal = 1 & G(X(outVal = (inVal + 1)))
                    '''

class Comparator(Contract):
    '''
    N-based comparator
    '''
    INPUT_PORTS = [('val_in', CounterSignal)]
    OUTPUT_PORTS = [('is_eq', DelayedSignal), ('n', IntegerParameter)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' G((val_in = n) -> is_eq) &
                     G(!(val_in = n) -> !is_eq) & 
                     G(n>=0 & n<=10)
                    '''


class Trigger(Contract):
    '''
    N-based comparator
    '''
    INPUT_PORTS = [('reset', ControlSignal)]
    OUTPUT_PORTS = [('trig', DelayedSignal), ('n', IntegerParameter), ('c', CounterSignal)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''c = 0 & 
                    G(c >= n <-> trig) &
                    G(reset -> (X (c = 0))) &
                    G((c < n) & !reset -> ((X (c) = c + 1) )) & 
                    G((c >= n)& !reset -> ((X (c = n)) )) & 
                    G(n>=0 & n<=10)
                    '''

class Comparator3(Contract):
    '''
    3-based comparator
    '''
    INPUT_PORTS = [('val_in', IntegerSignal), ('clk', Clk)]
    OUTPUT_PORTS = [('is_eq', DigitalSignal),]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !is_eq & G((val_in = 1) -> X is_eq) &
                     G(!(val_in = 1) -> X !is_eq)
                    '''

class Invert(Contract):
    '''
    invert
    '''
    INPUT_PORTS = [('in', ControlSignal),]
    OUTPUT_PORTS = [('out', ControlSignal),]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''G((out) <-> !in)'''
    # GUARANTEES = ''' out = !in'''

class FlipFlop(Contract):
    '''
    a flipflop
    '''
    INPUT_PORTS = [('d', DataSignal),  ('en', ControlSignal)]
    OUTPUT_PORTS = [('q', FlipFlopOut)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !q &
                     G(en -> (d <-> X q)) &
                     G(!en -> (q <-> X q))
                    '''

# class ADC2(Contract):
#     '''
#     an AD converter
#     '''
#     INPUT_PORTS = [('cs', DigitalSignal),  ('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit)]
#     OUTPUT_PORTS = [('miso', SPIMiso)]
#     ASSUMPTIONS = '''G(cs -> (X !cs & X2 !cs ))'''
#     GUARANTEES = ''' !miso &  (!cs -> X !miso) & G(cs -> ( anbit_0 <-> X miso)) &
#                      G(cs -> ( anbit_1 <-> X2 miso))
#                      & G((!cs & X!cs) -> (X2 ! miso))
#                     '''

class ADC2(Contract):
    '''
    an AD converter
    '''
    INPUT_PORTS = [('cs', SPICs),  ('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit)]
    OUTPUT_PORTS = [('miso', SPIMiso)]
    ASSUMPTIONS = '''!cs '''
    GUARANTEES = ''' !miso & X !miso &
                     G((!cs & X cs & X2 cs) -> ( X2 (miso) <-> X anbit_0)) &
                     G((!cs & X cs & X2 cs & X3 cs) -> ( X3 (miso) <-> X anbit_1)) &
                     G((!cs & X cs & X2 cs & X3 cs) -> ( X4 (!miso) )) &
                     G((!cs) -> (X(! miso) )) &
                     G((!cs) -> ((! miso) )) &
                     G((cs & X cs & X2 cs & X3 cs) -> ( X4 ( !miso))) 
                     '''

class ADC3(Contract):
    '''
    an AD converter
    '''
    INPUT_PORTS = [('cs', SPICs),
                   ('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit), ('anbit_2', AnalogDataBit)]
    OUTPUT_PORTS = [('miso', SPIMiso)]
    ASSUMPTIONS = '''!cs '''
    GUARANTEES = ''' !miso & X !miso &
                     G((!cs & X cs & X2 cs) -> ( X2 (miso) <-> X anbit_0)) &
                     G((!cs & X cs & X2 cs & X3 cs) -> ( X3 (miso) <-> X anbit_1)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs) -> ( X4 (miso) <-> X anbit_2)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs) -> ( X5 (!miso) )) &
                     G((cs & X cs & X2 cs & X3 cs & X4 cs) -> ( X5 (!miso) )) &
                     G((!cs) -> (X(! miso) )) &
                     G((!cs) -> ((! miso) )) 
                     '''

class ADC8(Contract):
    '''
    an AD converter
    '''
    INPUT_PORTS = [('cs', SPICs),
                   ('anbit_0', AnalogDataBit), ('anbit_1', AnalogDataBit),
                   ('anbit_2', AnalogDataBit), ('anbit_3', AnalogDataBit),
                   ('anbit_4', AnalogDataBit), ('anbit_5', AnalogDataBit),
                   ('anbit_6', AnalogDataBit), ('anbit_7', AnalogDataBit), ]
    OUTPUT_PORTS = [('miso', SPIMiso)]
    ASSUMPTIONS = '''!cs '''
    GUARANTEES = ''' !miso & X !miso &
                     G((!cs & X cs & X2 cs ) -> ( X2 (miso) <-> X anbit_0)) &
                     G((!cs & X cs & X2 cs & X3 cs ) -> ( X3 (miso) <-> X anbit_1)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs ) -> ( X4 (miso) <-> X anbit_2)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs & X5 cs ) -> ( X5 (miso) <-> X anbit_3)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs & X5 cs & X6 cs ) -> ( X6 (miso) <-> X anbit_4)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs & X5 cs & X6 cs & X7 cs ) -> ( X7 (miso) <-> X anbit_5)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs & X5 cs & X6 cs & X7 cs & X8 cs ) -> ( X8 (miso) <-> X anbit_6)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs & X5 cs & X6 cs & X7 cs & X8 cs & X9 cs) -> ( X9 (miso) <-> X anbit_7)) &
                     G((!cs & X cs & X2 cs & X3 cs & X4 cs & X5 cs & X6 cs & X7 cs & X8 cs & X9 cs) -> ( X10 (!miso) )) &
                     G((cs & X cs & X2 cs & X3 cs & X4 cs & X5 cs & X6 cs & X7 cs & X8 cs & X9 cs) -> ( X10 (!miso) )) &
                     G((!cs) -> (X(! miso) )) &
                     G((!cs) -> ((! miso) )) 
                     '''


class ADC1(Contract):
    '''
    an 1bit AD converter
    '''
    INPUT_PORTS = [('cs', SPICs),  ('anbit_0', AnalogDataBit)]
    OUTPUT_PORTS = [('miso', SPIMiso)]
    ASSUMPTIONS = '''!cs '''
    GUARANTEES = ''' !miso & X !miso &
                     G((!cs & X cs & X2 cs) -> ( X2 (miso) <-> X anbit_0)) &
                     G((!cs) -> (X (! miso)))&
                     G((!cs & X2 !cs) -> (X2 (! miso)))&
                     G((cs & X cs) -> (X2 ( !miso)))
                    '''

# class ADC1(Contract):
#     '''
#     an 1bit AD converter
#     '''
#     INPUT_PORTS = [('cs', DigitalSignal),  ('anbit_0', AnalogDataBit)]
#     OUTPUT_PORTS = [('miso', SPIMiso)]
#     ASSUMPTIONS = '''!cs & G(cs -> (X !cs & X2 !cs ))'''
#     GUARANTEES = ''' !miso & X !miso &
#                      G(cs -> ( X2 (miso) <-> anbit_0)) &
#                      G(!cs -> (X2 (! miso)))
#                     '''