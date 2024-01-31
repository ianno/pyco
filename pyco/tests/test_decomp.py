'''
In this file there is a collection of tests related to the spec decomposition feature
It uses files from pycox/examples/example_decomp
Add reference
'''


import pytest
from pyco.examples.example_decomp import *
from pyco.spec_decomposition import *


# @pytest.fixture
# def cS():
#     '''
#     micro
#     '''
#     comp = S('S')
#     lib_c = LibraryComponent('S', comp)
#     return lib_c
#
# @pytest.fixture
# def cC():
#     '''
#     micro
#     '''
#     comp = C('C')
#     lib_c = LibraryComponent('C', comp)
#     return lib_c


def test_a():

    s = S('S')
    c = C('C')
    s.connect_to_port(s.a, c.a)

    assert not c.is_refinement(s)

def test_b():

    s = S('S')
    c = Cb('C')
    s.connect_to_port(s.a, c.a)
    s.connect_to_port(s.b, c.b)

    assert c.is_refinement(s)

def test_c():

    s = Sr('Sr')

    clusters = decompose_spec([s])
    print(clusters)
    assert len(clusters) == 2

def test_d():

    s = Sd('Sd')

    clusters = decompose_spec([s])
    print(clusters)
    assert len(clusters) == 2


def test_sound0():

    s = Sound0('Sound0')

    clusters = decompose_spec([s])
    print(clusters)
    assert len(clusters) == 1

def test_sound1():

    s = Sound1('Sound1')

    clusters = decompose_spec([s])
    print(clusters)
    assert len(clusters) == 2