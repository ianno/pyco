'''
example_experiments.py

In this file there is a collection of tests related to generic experiments

Author: Antonio Iannopollo
'''


from pyco.contract import Contract, BaseTypeBool, BaseTypeInt, BaseTypeFloat, ParameterInt
from pyco.library import (ContractLibrary, LibraryComponent,
                          LibraryPortMapping, LibraryCompositionMapping)
from pyco.synthesis import SynthesisInterface
from pyco import LOG


#let's start with types
class IntT(BaseTypeInt):
    '''
     type
    '''

class ParamIntT(ParameterInt):
    '''
     type
    '''

class BoolT(BaseTypeBool):
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

class SpecAlt(Contract):
    '''
    Always closed if everything is fine
    '''
    INPUT_PORTS = [('i1', IntT)]
    OUTPUT_PORTS = [('o1', IntT)]
    ASSUMPTIONS = 'G(i1>=1)'
    GUARANTEES = '''G(i1=4 -> o1=5)''' #& G(i1=4 -> o1=5)


class SpecNext(Contract):
    '''
    test
    '''
    INPUT_PORTS = [('i', IntT)]
    OUTPUT_PORTS = [('o', BoolT)]
    ASSUMPTIONS = '''G(i>=1)'''
    GUARANTEES = '''(i>=1) -> (  X !o & X2 !o & X3 o)
                     '''

class ElemNext(Contract):
    '''
    elem with param
    '''
    INPUT_PORTS = [('i', IntT)]
    OUTPUT_PORTS = [('o', BoolT), ('n', ParamIntT)]
    ASSUMPTIONS = '''G(i>=1)'''
    GUARANTEES = ''' ((n = 0) -> (X o)) &
                       ((n = 1) -> (X !o & X2 o)) &
                       ((n = 2) -> (X !o & X2 !o & X3 o)) &
                       (n>=0 & n<10)
                     '''
    

class SCPExampleElemA(Contract):
    '''
    elem with param
    '''
    INPUT_PORTS = [('x', BoolT)]
    OUTPUT_PORTS = [('y', BoolT)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !y & G(x <-> Xy)
                     '''

class SCPExampleElemB(Contract):
    '''
    elem with param
    '''
    INPUT_PORTS = [('v', BoolT)]
    OUTPUT_PORTS = [('w', BoolT), ('z', BoolT)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !w & G(v <-> Xw) & G(!z <-> w)
                     '''

class SCPExampleElemC(Contract):
    '''
    elem with param
    '''
    INPUT_PORTS = []
    OUTPUT_PORTS = [('ob', BoolT)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !ob & G(ob <-> X!ob)
                     '''

    
class SCPExampleSpec(Contract):
    '''
    elem with param
    '''
    INPUT_PORTS = [('i', BoolT)]
    OUTPUT_PORTS = [('o', BoolT)]
    ASSUMPTIONS = '''true'''
    GUARANTEES = ''' !o & X!o & G(i <-> X2o)'''
    # GUARANTEES = ''' G(i <-> X2o)'''