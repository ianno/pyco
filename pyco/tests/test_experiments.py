'''
test_eps.py

In this file there is a collection of tests related to the Electrical Power System (EPS)
problem.
It uses files from pycox/examples/example_eps
Add reference

Author: Antonio Iannopollo
'''


import pytest
from pyco.examples.example_experiments import *
from pyco.contract import CompositionMapping


@pytest.fixture
def diff():
    '''
    abstract generator
    '''
    comp = Diff('Diff')
    return LibraryComponent('Diff', comp)

@pytest.fixture
def dirty_diff():
    '''
    abstract generator
    '''
    comp = DirtyDiff('DirtyDiff')
    return LibraryComponent('DirtyDiff', comp)

@pytest.fixture
def fan_out():
    '''
    abstract generator
    '''
    comp = FanOut('FanOut')
    return LibraryComponent('FanOut', comp)

@pytest.fixture
def compl():
    '''
    abstract generator
    '''
    comp = Complement('Compl')
    return LibraryComponent('Compl', comp)

@pytest.fixture
def lib(diff, dirty_diff, fan_out, compl):
    '''
    returns a populated library with only the AC generators
    '''
    library = ContractLibrary('diff_lib')

    library.add(diff)
    library.add(dirty_diff)
    library.add(fan_out)
    library.add(compl)

    library.verify_library()

    #add type compatibilities
    library.add_type(IntT)
    library.add_type(FloatT)
    library.add_type(StringT)

    # library.add_type_compatibility(GeneratorT, ACGenContactorT)

    return library






def test_spec_1(lib):
    '''
    Performs simple synthesis
    '''

    spec1 = Spec('G1')

    interface = SynthesisInterface(lib, [spec1])

    interface.synthesize(strict_out_lib_map=False,
                             library_max_redundancy=2,
                             limit=3,
                             minimize_components=False,
                             minimize_ports=False,
                             filename='exp',
                             visualize=True,
                             decompose=False)

def test_manual(lib):
    '''
    Manual check
    '''

    spec1 = Spec('G1')

    interface = SynthesisInterface(lib, [spec1])

    fan_out = interface.get_component('FanOut')
    interface.use_component(fan_out)

    interface.synthesize(strict_out_lib_map=False,
                             library_max_redundancy=2,
                             limit=1,
                             minimize_components=False,
                             minimize_ports=False,
                             filename='exp',
                             visualize=True,
                             decompose=False)