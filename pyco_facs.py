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
parser.add_argument('experiment', help='run the experiments from FACS2016',
                    choices=['1', '2', '3', '4', '5', '6', '7', '8', '9', 'all'], default='all')

if __name__ == "__main__":

    args = parser.parse_args()

    if args.experiment != 'all':
        print 'Running EPS test in pyco-dev/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec...\n' % args.experiment
        pytest.main(['-s', 'pyco-dev/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec' % args.experiment])
    else:
        print 'Running 9 EPS tests in pyco-dev/tests/test_eps_facs.py::test_synth_6_10_dc_*...\n'
        pytest.main(['-s', '-k test_synth_6_10_dc_', 'pyco-dev/tests/test_eps_facs.py'])