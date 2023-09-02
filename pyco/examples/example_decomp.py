'''
example_decomp.py

In this file there is a collection of tests related to the spec decomposition feature

Author: Antonio Iannopollo,
'''


from pyco.contract import Contract, BaseTypeBool, BaseTypeInt, BaseTypeFloat, ParameterInt
from pyco.library import (ContractLibrary, LibraryComponent,
                          LibraryPortMapping, LibraryCompositionMapping)
from pyco.synthesis import SynthesisInterface
from pyco import LOG



class S(Contract):
    '''
    base spec.
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = ['a', 'b']
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''G(a | b)'''

class C(Contract):
    '''
    base spec.
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = ['x', 'y', 'a']
    ASSUMPTIONS = '''G(a=x) -> true'''
    GUARANTEES = '''G(a=x) & G(x | y)'''

class Cb(Contract):
    '''
    base spec.
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = ['x', 'y', 'a', 'b']
    ASSUMPTIONS = '''G(a=x & b=y) -> true'''
    GUARANTEES = '''G(a=x & b=y) & G(x | y)'''

class Sr(Contract):
    '''
    base spec.
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = [ 'a', 'b', 'c', 'd', 'e', 'f','g', 'h']
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''G(a=b & b=c & a=h) & G(d=e & e=f & d=g)'''


class Sd(Contract):
    '''
    base spec.
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = [ ('a', BaseTypeInt), ('b', BaseTypeInt), ('c', BaseTypeInt),
                        ('d', BaseTypeInt), ('e', BaseTypeInt), ('f', BaseTypeInt)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''G((a=b+1) & (b=c+1)) & G((d=e+1) & (e=f+1))'''

class Sound0(Contract):
    '''
    base spec.
    '''
    INPUT_PORTS = ['p']
    OUTPUT_PORTS = [ 'a', 'b', 'c',]
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''G(p -> (a | (b & c)))'''

class Sound1(Contract):
    '''
    base spec.
    '''
    INPUT_PORTS = ['p']
    OUTPUT_PORTS = [ 'v', 't', 'w', 'z']
    ASSUMPTIONS = '''true'''
    GUARANTEES = '''G( (p -> X(v & !t) ) & (!p -> X(!v & t) ) & (v -> X(!w & z) ) & (!v -> X(w & !z) ) )'''