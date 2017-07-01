'''
.. module:: main
:synopsis: This module contains the main function of the tool.
            It parses inputs and calls the appropriate functions.

.. moduleauthor:: Antonio Iannopollo <antonio@berkeley.edu>

'''

import argparse
import pytest
import sys, os

parser = argparse.ArgumentParser()
# parser.add_argument('--facs',
#                     choices=['1', '2', '3', '4', '5', '6', '7', '8', '9', "all"],
#                     help='run the experiments from FACS2016')
#
# parser.add_argument('--edg',
#                     choices=['1'],
#                     help='run the experiments related to Embedded Design')

parser.add_argument('-m', '--minimize',
                    choices=['components', 'ports', 'cost'], default='ports',
                    help='Enable the synthesis of the optimal solution minimizing the selected cost function')
parser.add_argument('-N', '--max-size',
                    type=int, default=10,
                    help='Set the maximum number of components in the solution')

parser.add_argument('-lr', '--lib-redundancy',
                    type=int, default=2,
                    help='Set the level of redundancy of the component library')

parser.add_argument('-o', '--output',
                    type=int, default=2,
                    help='Set the output file name')

if __name__ == "__main__":

    args = parser.parse_args()

    # if args.facs is not None:
    #     if args.facs != 'all':
    #         print 'Running EPS test in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec...\n' % args.facs
    #         pytest.main(['-s', 'pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec' % args.facs])
    #     elif args.facs == 'all':
    #         print 'Running 9 EPS tests in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_*...\n'
    #         pytest.main(['-s', '-k test_synth_6_10_dc_', 'pyco/tests/test_eps_facs.py'])
    #
    # if args.edg is not None:
    #     if args.edg == '1':
    #         print 'Running EDG test in pyco/tests/test_edg_motor.py::test_ltl_spec_med...\n'
    #         pytest.main(['-s', 'pyco/tests/test_edg_motor.py::test_ltl_spec_med'])
