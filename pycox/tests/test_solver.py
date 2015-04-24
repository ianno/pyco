'''
test of the constraint solver interface

Author: Antonio Iannopollo
'''

import pytest
import logging

from pycox.tests.test_rcpl import (populated_library, comp_a, comp_b, comp_ab, comp_meta, library)

LOG = logging.getLogger()

@pytest.mark.trylast
def test_all_names(populated_library):
    '''
    print all names
    '''
    (ports, contracts, components) = populated_library.smt_manager._enumerate_names()

    LOG.debug('Ports')
    LOG.debug(ports)
    LOG.debug('Contracts')
    LOG.debug(contracts)
    LOG.debug('Components')
    LOG.debug(components)

    assert True

