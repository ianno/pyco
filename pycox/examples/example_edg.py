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

#Now let's include some components
class AbstractGenerator(Contract):
    '''
    generator OK at beginning. Once broken stays broken.
    if fails eventually close the contactor
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACGenContactorT)]
    ASSUMPTIONS = '!fail & G(fail -> X fail)'
    GUARANTEES = 'G(fail -> F ! c)'



#now add specs

#case 0: 1gen-2contactors -> 2 ports
class GenIsolation0(Contract):
    '''
    generator 1 is eventually disconnected if faulty.
    '''
    INPUT_PORTS = [('fail1', GeneratorT)]
    OUTPUT_PORTS = [('c1', ACContactorT)]
    ASSUMPTIONS = '''!fail1  &
                     G(fail1 -> Xfail1)'''
    #ASSUMPTIONS = '''!fail1 & G(fail1 -> Xfail1) '''
    GUARANTEES = 'G(fail1 -> F!c1)'
