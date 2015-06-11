'''
Synthesizer interface

Author: Antonio Iannopollo
'''

import itertools
from pycox import LOG
from pycox.z3_interface import Z3Interface, NotSynthesizableError



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

        self.same_block_pairs = set()
        self.distinct_map = set()

        self.solver_interface = Z3Interface(library)


    def same_block_constraint(self, port_list):
        '''
        Assert a set of ports to be implemented by the same block
        '''

        for (port_1, port_2) in itertools.combinations(port_list, 2):
           self.same_block_pairs.add((port_1.base_name, port_2.base_name))

    def distinct_ports_constraints(self, port_list):
        '''
        specifies a set of ports that cannot have same mapped
        ports
        '''
        for (port_1, port_2) in itertools.combinations(port_list, 2):
           self.distinct_map.add((port_1.base_name, port_2.base_name))

    def synthesize(self):
        '''
        call for synthesis
        '''

        self.solver_interface.synthesize(self.spec_contract,
                                         same_block_constraints=self.same_block_pairs,
                                         distinct_mapping_constraints=self.distinct_map)
