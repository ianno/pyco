'''
This module is the main interface to the solver functions.

Author: Antonio Iannopollo
'''

import logging

LOG = logging.getLogger()
LOG.debug('in solver.py')


def verify_specification(spec_contract, design_contract, library):
    '''
    Returns True if design_contract refines spec_contract.
    Library is used to speed up the verification process.
    Uses a modified implementation of the RCPL algorithm.

    :param spec_contract: A Contract representing the specification
                         to be satisfied
    :type spec_contract: pycox.contract.Contract

    :param design_contract: a contract representing the user defined
                           design
    :type design_contract: pycox.contract.Contract

    :param library: a library object

    :returns: boolean
    '''
    pass


def synthesize_design(spec_contract, partial_design_contract, library):
    '''
    Given a partial design, this method returns a fully specified design
    contract which refines the specification contract. Possible candidate
    solutions are computed picking contracts from the provided library

    :param spec_contract: A contract representing the specification to be
                         satisfied
    :type spec_contract: pyco.contract.Contract

    :param partial_design_contract: a Contract representing a partial design.
    :type partial_design_contract: pycox.contract.Contract

    :param library: a library object

    :returns: a fully specified design contract which refines spec_contract,
             or None if no solution is found
    '''
    pass
