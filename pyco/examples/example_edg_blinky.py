'''
example_edg_motor.py

In this file there is a collection of tests related to the Electronic Device Generation project.
Add reference

Author: Antonio Iannopollo, Rohit Ramesh, Richard Lin
'''


from pyco.contract import Contract, BaseTypeBool, BaseTypeInt, BaseTypeFloat
from pyco.library import (ContractLibrary, LibraryComponent,
                          LibraryPortMapping, LibraryCompositionMapping)
from pyco.synthesis import SynthesisInterface
from pyco import LOG

#let's start with types
class VarVoltage(BaseTypeInt):
    '''
    variable Voltage
    '''
    pass

class VarCurrent(BaseTypeInt):
    '''
    variable current
    '''
    pass

class Voltage(BaseTypeBool):
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

class IOPin(BaseTypeBool):
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

class DigitalState(BaseTypeBool):
    '''
    button state
    '''
    pass

class ButtonState(DigitalState):
    '''
    button state
    '''
    pass

class LedState(DigitalState):
    '''
    button state
    '''
    pass

class GND(BaseTypeBool):
    '''
    ground
    '''
    pass


#Now let's include some components
class Button(Contract):
    '''
    button. Need to add that vin and iino are a logic port,
    ie, need to be connected to same logic port
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', VarVoltage), ('iin', VarCurrent)]
    OUTPUT_PORTS = [('vout', VarVoltage), ('iout', VarCurrent), ('bout', ButtonState)]
    ASSUMPTIONS = 'G(vin >= 0 & vin <= 36) & G(iin >= 1 & iin <= 2)'
    GUARANTEES = '''G(vout = vin) & G(iout = 0 | iout = iin)'''

class PowerAdapter3V(Contract):
    '''
    MCU
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = [('gnd', GND), ('vout', VarVoltage)]
    GUARANTEES = '''G(vout = 3)'''

class LED(Contract):
    '''
    Led. Need to add that vin and iino are a logic port,
    ie, need to be connected to same logic port
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', VarVoltage), ('iin', VarCurrent), ('lin', LedState)]
    OUTPUT_PORTS = [('vout', VarVoltage), ('iout', VarCurrent), ('lout', LedState)]
    ASSUMPTIONS = '''G(vin >= 0 & vin <= 36) 
                     & G(iin >= 1 & iin <= 2) 
                     & G(vin > 0 -> lin) & G(vin = 0 -> !lin)'''
    GUARANTEES = '''G(vout = vin) & G(iout = iin)
                    & G(vout > 0 -> lout) & G(vout = 0 -> !lout)'''


class Apm3v3(Contract):
    '''
    Arduino Pro Micro 3v3
    '''
    INPUT_PORTS = [('gnd', GND), ('vin', VarVoltage), ('iin', VarCurrent),
                   ('gvin1', VarVoltage), ('giin1', VarCurrent), ('gst1', DigitalState),
                   ('gvin2', VarVoltage), ('giin2', VarCurrent), ('gst2', DigitalState),
                   ('gvin3', VarVoltage), ('giin3', VarCurrent), ('gst3', DigitalState),
                   ('gvin4', VarVoltage), ('giin4', VarCurrent), ('gst4', DigitalState),]
    OUTPUT_PORTS = [('p5vout', VarVoltage), ('p3vout', VarVoltage),
                    ('i5out', VarCurrent), ('i3out', VarCurrent),
                    ('gvout1', VarVoltage), ('giout1', VarCurrent), ('gout1', DigitalState),
                    ('gvout2', VarVoltage), ('giout2', VarCurrent), ('gout2', DigitalState),
                    ('gvout3', VarVoltage), ('giout3', VarCurrent), ('gout3', DigitalState),
                    ('gvout4', VarVoltage), ('giout4', VarCurrent), ('gout4', DigitalState),]
    ASSUMPTIONS = '''G(vin >= 45 & vin <= 55) 
                     & G(iin >= 0 & iin <= 200) 
                     & G(gvin1 = 0 | gvin1 = 3) & G(giin1 <= 50)
                     & G(gvin2 = 0 | gvin2 = 3) & G(giin2 <= 50)
                     & G(gvin3 = 0 | gvin3 = 3) & G(giin3 <= 50)
                     & G(gvin4 = 0 | gvin4 = 3) & G(giin4 <= 50)'''
    GUARANTEES = '''G(p5vout = 5) & G(p3vout = 3)
                     & G(gvout1 = 0 | gvout1 = 3) & G(giout1 = 50) & G(gvout1 > 0 -> gout1) & G(gvout1 = 0 -> !gout1)
                     & G(gvout2 = 0 | gvout2 = 3) & G(giout2 = 50) & G(gvout2 > 0 -> gout2) & G(gvout2 = 0 -> !gout2)
                     & G(gvout3 = 0 | gvout3 = 3) & G(giout3 = 50) & G(gvout3 > 0 -> gout3) & G(gvout3 = 0 -> !gout3)
                     & G(gvout4 = 0 | gvout4 = 3) & G(giout4 = 50) & G(gvout4 > 0 -> gout4) & G(gvout4 = 0 -> !gout4)'''


    class zerospec(Contract):
        '''
        base spec. Say you want a button and LED
        '''
        INPUT_PORTS = [ ]
        OUTPUT_PORTS = [ ]