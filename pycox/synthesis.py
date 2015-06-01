'''
Synthesizer interface

Author: Antonio Iannopollo
'''

import itertools
import logging
from pycox.z3_interface import Z3Interface

LOG = logging.getLogger()


class SynthesisInterface(object):
    '''
    Interface for synthesis
    '''

    def __init__(self, spec_contract, library):
        '''
        constructor
        '''

        self.spec_contract = spec_contract
        self.library = library

        self.solver_interface = Z3Interface(library)


    def same_block_constraint(self, port_name_list):
        '''
        Assert a set of ports to be implemented by the same block
        '''

        for (port_1, port_2) in itertools.product(port_name_list):
            pass

    def synthesize(self):
        '''
        call for synthesis
        '''

        self.solver_interface.synthetize(self.spec_contract)
