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
class BreakableT(BaseType):
    '''
    an object that can break
    '''
    pass

class GeneratorT(BreakableT):
    '''
    generator type
    '''
    pass

class RectifierT(BreakableT):
    '''
    Rectifier
    '''
    pass

class ContactorT(BaseType):
    '''
    Generic Contactor
    '''
    pass

class ACContactorT(ContactorT):
    '''
    AC Contactor
    '''
    pass

class DCContactorT(ContactorT):
    '''
    DC Contactor
    '''
class BusContactorT(ContactorT):
    '''
    Bus Contactor
    '''

#Now let's include some components
class AbstractGenerator(Contract):
    '''
    generator OK at beginning. Once broken stays broken.
    if fails eventually close the contactor
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACContactorT)]
    ASSUMPTIONS = '!fail & G(fail -> X fail)'
    GUARANTEES = 'G(fail -> F ! c)'

class DumbGenerator(Contract):
    '''
    Always open
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACContactorT)]
    ASSUMPTIONS = '!fail'
    GUARANTEES = 'G(! c)'

class StdGenerator(Contract):
    '''
    closes the contactor if everything is ok
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACContactorT)]
    ASSUMPTIONS = '!fail & G(fail -> X fail)'
    GUARANTEES = 'G(fail -> ! c) & G(!fail -> c)'

class SlowGenerator(Contract):
    '''
    closes the contactor if everything is ok.
    lock after 1 step
    '''
    INPUT_PORTS = [('fail', GeneratorT)]
    OUTPUT_PORTS = [('c', ACContactorT)]
    ASSUMPTIONS = '!fail & G(fail -> X fail)'
    GUARANTEES = 'c & G(fail -> X ! c) & G(!fail -> c)'
