'''
This module builds the structure converting the contract library to datatypes
for the Z3 SMT solver

Author: Antonio Iannopollo
'''

from pycolite.formula import (Conjunction, Disjunction, Negation,
                          Implication, Equivalence, TrueFormula, FalseFormula)
from z3 import *

from pyco import LOG

LOG.debug('in z3_library_conversion')


class Z3Library(object):
    '''
    maps library to a a set of Z3 variables
    '''


    def __init__(self, library, context=None):
        '''
        store the library for further processing
        :param library:
        :param context:
        '''

        self.library = library
        self.context = context
        self.connection_map = {}

    def preprocess(self, spec):
        '''
        preprocess library and determines which components can be connected together
        '''

        self.library.preprocess_with_spec(spec)
        self.spec = spec
        self.use_flags = {}
        self.level_index = {}


        for contract in self.library.all_contracts:
            self.use_flags[contract] = Int('%s' % contract.unique_name, self.context)
            self.level_index[contract] = Int('lev_%s' % contract.unique_name, self.context)


