'''
test of module contract.py

Author: Antonio Iannopollo
'''

import pytest
from pycox.contract import Contract, Port

class TrueContract(Contract):
    '''
    define a test true contract, one input and one output
    '''
    ASSUMPTIONS = 'false'
    GUARANTEES = 'true'
    INPUT_PORTS = ['a']
    OUTPUT_PORTS = ['b']

class FalseContract(Contract):
    '''
    A contract that never works, but it does so everywhere
    '''
    ASSUMPTIONS = 'true'
    GUARANTEES = 'false'
    INPUT_PORTS = ['c']
    OUTPUT_PORTS = ['d']

@pytest.fixture(scope='module', params=[TrueContract, FalseContract])
def inst_contract(request):
    '''
    Instantiate a TrueContract object
    '''

    return request.param('C')



def test_contract_contruction(inst_contract):
    '''
    Test the new style contructor
    '''

    print inst_contract
    assert True

def test_contract_compatibility(inst_contract):
    '''
    Expects false for TrueContract, true for False Contract, anything from others
    '''
    if type(inst_contract) is TrueContract:
        assert not inst_contract.is_compatible()
    elif type(inst_contract) is FalseContract:
        assert inst_contract.is_compatible()
    else:
        print inst_contract.is_compatible()
        assert True

def test_contract_consistency(inst_contract):
    '''
    Expects true for TrueContract, false for False Contract, anything from others
    '''
    if inst_contract is TrueContract:
        assert inst_contract.is_consistent()
    elif inst_contract is FalseContract:
        assert not inst_contract.is_consistent()
    else:
        print inst_contract.is_consistent()
        assert True

