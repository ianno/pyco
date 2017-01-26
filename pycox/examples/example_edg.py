'''
example_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
Add reference

Author: Antonio Iannopollo
'''


from pycox.contract import Contract, BaseType
from pycox.library import (ContractLibrary, LibraryComponent,
                            LibraryPortMapping, LibraryCompositionMapping)
from pycox.synthesis import SynthesisInterface
from pycox import LOG

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

class VariableVoltage(Voltage):
    '''
    input or output of fixed voltage @5V
    '''
    min = None
    max = None

    def __init__(self, min, max):
        '''
        init values
        '''
        self.min = min
        self.max = max


class IOPin(BaseType):
    '''
    input/output pin
    '''
    pass

class Device(BaseType):
    '''
    used to describe state of simple devices like LEDs, etc.
    '''
    pass

class LEDDevice(Device):
    '''
    used to describe state of simple devices like LEDs, etc.
    '''
    pass

class GND(BaseType):
    '''
    ground
    '''
    pass


class I2C(Voltage5V):
    '''
    I2C bus
    '''
    pass


class SDA(I2C):
    '''
    Serial Data I2C line
    '''
    pass


class SCL(I2C):
    '''
    Serial Clock I2C line
    '''
    pass

class SCLSlave(SCL):
    '''
    Serial Clock I2C slave line
    '''
    pass

class SCLMaster(SCL):
    '''
    Serial Clock I2C master line
    '''
    pass

#Now let's include some components
class LED(Contract):
    '''
    Basic LED
    '''
    INPUT_PORTS = [('gnd', GND), ('pwr', Voltage5V)]
    OUTPUT_PORTS = [('led', LEDDevice)]
    ASSUMPTIONS = 'true'
    GUARANTEES = 'true'

class DoubleLED(Contract):
    '''
    Basic LED
    '''
    INPUT_PORTS = [('gnd', GND), ('pwr_l', Voltage5V), ('pwr_r', Voltage5V)]
    OUTPUT_PORTS = [('led_l', LEDDevice), ('led_r', LEDDevice)]
    ASSUMPTIONS = 'true'
    GUARANTEES = 'true'

class Microcontroller(Contract):
    '''
    Basic micro
    '''
    INPUT_PORTS = [('gnd', GND), ('pwr', Voltage5V)]
    OUTPUT_PORTS = [('io', IOPin)]
    ASSUMPTIONS = 'true'
    GUARANTEES = 'true'


class PowerAdapter5V(Contract):
    '''
    Basic micro
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = [('gnd', GND), ('pwr', Voltage5V)]
    ASSUMPTIONS = 'true'
    GUARANTEES = 'true'

#now add specs

#case 0: 1gen-2contactors -> 2 ports
class SimpleLED(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = [('led', LEDDevice)]
    ASSUMPTIONS = '''true'''
    #ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) '''
    GUARANTEES = 'true'
