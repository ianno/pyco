'''
example_edg.py

In this file there is a collection of tests related to the Electronic Device Generation project.
Add reference

Author: Antonio Iannopollo
'''


from pycox.contract import Contract, BaseType, IntRangeType, AnyType
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

class VariableVoltage(IntRangeType):
    '''
    input or output of variable voltage 3-5V
    '''

    min = None
    max = None

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
    input or output of fixed voltage @5V
    '''
    pass

class VariableVoltage3to5(VariableVoltage):
    '''
    input or output of variable voltage 3-5V
    '''

    min = 3
    max = 5

class VariableVoltage5(VariableVoltage):
    '''
    input or output of variable voltage 3-5V
    '''

    min = 5
    max = 5

class VariableVoltage3(VariableVoltage):
    '''
    input or output of variable voltage 3-5V
    '''

    min = 5
    max = 5


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

class GPIODriverT(BaseType):
    '''
    GPIO driver type
    '''
    pass

class LEDDriverT(BaseType):
    '''
    LED driver
    '''
    pass

class AclDriverT(BaseType):
    '''
    Accelerometer driver
    '''
    pass



#Now let's include some components
class LEDDriver(Contract):
    '''
    Led driver
    '''
    INPUT_PORTS = [('io', GPIODriverT)]
    OUTPUT_PORTS = [('led', LEDDriverT)]

class AclDriver(Contract):
    '''
    Led driver
    '''
    INPUT_PORTS = [('io', GPIODriverT)]
    OUTPUT_PORTS = [('acl', AclDriverT)]

class GPIODriver(Contract):
    '''
    GPIO driver
    '''
    INPUT_PORTS = [('gpio', IOPin)]
    OUTPUT_PORTS = [('io', GPIODriverT)]

class LEDGeneral(Contract):
    '''
    General LED
    '''

    INPUT_PORTS = [('led_ctrl', LEDDriverT), ('gnd', GND), ('pwr', Voltage5V)]
    OUTPUT_PORTS = [('led', Device)]

class Accelerometer(Contract):
    '''
    General LED
    '''

    INPUT_PORTS = [('acl_ctrl', AclDriverT), ('gnd', GND), ('pwr', Voltage3V)]
    OUTPUT_PORTS = [('acl', Device)]

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
    INPUT_PORTS = [('gnd', GND), ('vin', Voltage3V)]
    OUTPUT_PORTS = [('o1', IOPin), ('o2', IOPin), ('o3', IOPin), ('o4', IOPin)]

class LED(Contract):
    '''
    Basic LED
    '''
    INPUT_PORTS = [('gnd', GND), ('pwr', Voltage5V)]
    OUTPUT_PORTS = [('led', LEDDevice)]
    ASSUMPTIONS = 'true'
    GUARANTEES = 'true'

class LEDVar(Contract):
    '''
    Basic LED
    '''
    INPUT_PORTS = [('gnd', GND), ('pwr', VariableVoltage3to5)]
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

class SimpleEmpty(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = []
    ASSUMPTIONS = '''true'''
    GUARANTEES = 'true'