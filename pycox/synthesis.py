'''
Synthesizer interface

Author: Antonio Iannopollo
'''

import itertools
import logging

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

        pass
