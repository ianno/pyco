'''
example_experiments.py

In this file there is a collection of tests related to generic experiments

Author: Antonio Iannopollo
'''


from pyco.contract import Contract, BaseTypeBool, BaseTypeInt, BaseTypeFloat
from pyco.library import (ContractLibrary, LibraryComponent,
                          LibraryPortMapping, LibraryCompositionMapping)
from pyco.synthesis import SynthesisInterface
from pyco import LOG


#let's start with types
class IntT(BaseTypeInt):
    '''
     type
    '''

class FloatT(BaseTypeFloat):
    '''
    generator type
    '''
    pass

class StringT(BaseTypeInt):
    '''
    generator type
    '''
    pass




class FanOut(Contract):
    '''
    Always closed if everything is fine
    '''
    INPUT_PORTS = [('i', IntT)]
    OUTPUT_PORTS = [('o1', IntT), ('o2', IntT), ('o3', IntT)]
    ASSUMPTIONS = 'G(i > -2)'
    GUARANTEES = '''G(o1 = i-1) & G(o2 = i) & G(o3 = i * 2)'''


class Diff(Contract):
    '''
    Always closed if everything is fine
    '''
    INPUT_PORTS = [('i1', IntT), ('i2', IntT)]
    OUTPUT_PORTS = [('o1', IntT)]
    ASSUMPTIONS = 'G(i1 >= i2)'
    GUARANTEES = '''G(o1 = (i1-i2))'''

class Complement(Contract):
    '''
    Always closed if everything is fine
    '''
    INPUT_PORTS = [('i1', IntT)]
    OUTPUT_PORTS = [('o1', IntT)]
    ASSUMPTIONS = 'true'
    GUARANTEES = '''G(o1 = -i1)'''

class DirtyDiff(Contract):
    '''
    Always closed if everything is fine
    '''
    INPUT_PORTS = [('i1', IntT), ('i2', IntT)]
    OUTPUT_PORTS = [('o1', IntT)]
    ASSUMPTIONS = 'true'
    GUARANTEES = '''G(o1 = (i1-i2))'''



class Spec(Contract):
    '''
    Always closed if everything is fine
    '''
    INPUT_PORTS = [('i1', IntT)]
    OUTPUT_PORTS = [('o1', IntT)]
    ASSUMPTIONS = 'G(i1>=0)'
    GUARANTEES = '''G(i1=5 -> o1=6)''' #& G(i1=4 -> o1=5)
