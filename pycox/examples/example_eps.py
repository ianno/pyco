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
