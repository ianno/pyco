'''
example_edg_motor.py

In this file there is a collection of tests related to the Electronic Device Generation project.
Add reference

Author: Antonio Iannopollo, Rohit Ramesh, Richard Lin
'''


from pyco.contract import Contract, BaseType, IntRangeType
from pyco.library import (ContractLibrary, LibraryComponent,
                          LibraryPortMapping, LibraryCompositionMapping)
from pyco.synthesis import SynthesisInterface
from pyco import LOG

#let's start with types
class Voltage(BaseType):
    '''
    general Voltage
    '''
    pass


class Voltage5V(Voltage):
    '''
    input or output of fixed voltage @5V
    '''
    pass

class Voltage3V(Voltage):
    '''
    input or output of fixed voltage @3V
    '''
    pass

class Voltage12V(Voltage):
    '''
    input or output of fixed voltage @3V
    '''
    pass

class IOPin(BaseType):
    '''
    input/output pin
    '''
    pass

class IOPin3(IOPin):
    '''
    input/output pin
    '''
    pass

class Sensor(IOPin3):
    '''
    input/output pin
    '''
    pass

class HalfBDrive(IOPin3):
    '''
    input/output pin
    '''
    pass

class CurrentDrive(IOPin3):
    '''
    input/output pin
    '''
    pass

class IOPin12(IOPin):
    '''
    input/output pin
    '''
    pass

class GND(BaseType):
    '''
    ground
    '''
    pass


#Now let's include some components
class PowerAdapter12V(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = [('gnd', GND), ('vout', Voltage12V)]

class PowerAdapter5V(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = [('gnd', GND), ('vout', Voltage5V)]

class DcDcConverter12_3(Contract):
    '''
    DCDC 12 to 3
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', Voltage12V)]
    OUTPUT_PORTS = [('vout', Voltage3V)]

class DcDcConverter12_5(Contract):
    '''
    DCDC 12 to 5
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', Voltage12V)]
    OUTPUT_PORTS = [('vout', Voltage5V)]

class SimpleMCU(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', Voltage3V), ('i1', IOPin3), ('i2', IOPin3)]
    OUTPUT_PORTS = [('o1', IOPin3), ('o2', IOPin3), ('o3', IOPin3), ('o4', IOPin3)]

class SmallMCU(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', Voltage3V), ('i1', IOPin3)]
    OUTPUT_PORTS = [('o1', IOPin3), ('o2', IOPin3), ('o3', IOPin3),
                    ('o11', IOPin3), ('o12', IOPin3), ('o13', IOPin3),
                    ('o21', IOPin3), ('o22', IOPin3), ('o23', IOPin3)]
    ASSUMPTIONS = 'true'
    GUARANTEES = '''o1 & !o2 & !o3 &
                    G( (o1 & !i1 & X i1) -> (X !o1 & X o2 & X !o3)) &
                    G( (o1 & !i1 & X !i1) -> (X o1 & X !o2 & X !o3)) &
                    G( (o2 & !i1 & X i1) -> (X !o1 & X !o2 & X o3)) &
                    G( (o2 & !i1 & X !i1) -> (X !o1 & X o2 & X !o3)) &
                    G( (o3 & !i1 & X i1) -> (X o1 & X !o2 & X !o3)) &
                    G( (o3 & !i1 & X !i1) -> (X !o1 & X !o2 & X o3))
                 '''

class MCU(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', Voltage3V), ('i1', IOPin3), ('i2', IOPin3)]
    OUTPUT_PORTS = [('o1', IOPin3), ('o2', IOPin3), ('o3', IOPin3), ('o4', IOPin3)]
    ASSUMPTIONS = '!i1'
    GUARANTEES = '''o1 & !o2 & !o3 &
                    G( (o1 & !i1 & X i1) -> (X !o1 & X o2 & X !o3)) &
                    G( (o2 & !i1 & X i1) -> (X !o1 & X !o2 & X o3)) &
                    G( (o3 & !i1 & X i1) -> (X o1 & X !o2 & X !o3))
                 '''

class SimpleHalfBridge(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', Voltage12V), ('i1', IOPin3)]
    OUTPUT_PORTS = [('o1', IOPin12)]

class HalfBridge(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', Voltage12V), ('i1', IOPin3)]
    OUTPUT_PORTS = [('o1', IOPin12)]
    ASSUMPTIONS = 'true'
    GUARANTEES = '''G(i1 = o1)
                 '''

class SimpleReq(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = [('i1', IOPin3)]
    OUTPUT_PORTS = [('o1', IOPin12), ('o2', IOPin12), ('o3', IOPin12)]


class AlternateWaveReq(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = [('i1', IOPin3)]
    OUTPUT_PORTS = [('o1', IOPin12), ('o2', IOPin12), ('o3', IOPin12)]
    ASSUMPTIONS = '!i1 & GF(i1) & GF(!i1)'
    GUARANTEES = '''o1 & !o2 & !o3 &
                    G( (o1 & !i1 & X i1) -> (X !o1 & X o2 & X !o3)) &
                    G( (o2 & !i1 & X i1) -> (X !o1 & X !o2 & X o3)) &
                    G( (o3 & !i1 & X i1) -> (X o1 & X !o2 & X !o3))
                 '''