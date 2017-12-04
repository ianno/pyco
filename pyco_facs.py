'''
.. module:: main
:synopsis: This module contains the main function of the tool.
            It parses inputs and calls the appropriate functions.

.. moduleauthor:: Antonio Iannopollo <antonio@berkeley.edu>

'''

import argparse
import pytest
import sys, os

TIMEOUT_SEC = 1000

parser = argparse.ArgumentParser()
group = parser.add_mutually_exclusive_group()

group.add_argument('--all', help='run all the experiments from FACS 2016',
                   action="store_true")
group.add_argument('--eps20', help='run the EPS synthesis with a library of 20 elements.',
                   choices=['1', '2', '3', '4', '5', '6', '7', '8', '9', 'all'])
group.add_argument('--eps40', help='run the EPS synthesis with a library of 40 elements.',
                   choices=['1', '2', '3', '4', '5', '6', '7', '8', '9', 'all'])
group.add_argument('--eps20_ports', help='run the EPS synthesis with a library of 20 elements.'
                                         'Minimize number of ports.',
                   choices=['1', '2', '3', '4', '5', '6', '7', '8', '9', 'all'])
group.add_argument('--eps40_ports', help='run the EPS synthesis with a library of 40 elements.'
                                         'Minimize number of ports.',
                   choices=['1', '2', '3', '4', '5', '6', '7', '8', '9', 'all'])
group.add_argument('--eps20_comps', help='run the EPS synthesis with a library of 20 elements.'
                                         'Minimize number of components.',
                   choices=['1', '2', '3', '4', '5', '6', '7', '8', '9', 'all'])
group.add_argument('--eps40_comps', help='run the EPS synthesis with a library of 40 elements.'
                                         'Minimize number of components.',
                   choices=['1', '2', '3', '4', '5', '6', '7', '8', '9', 'all'])
group.add_argument('--inc20wt', help='run the incremental EPS synthesis with a library of 20 elements. '
                                     'Use types and user hints.',
                   choices=['1', '2', '3', '4', '5', 'all'])
group.add_argument('--inc40wt', help='run the incremental EPS synthesis with a library of 40 elements'
                                   'Use types and user hints.',
                   choices=['1', '2', '3', '4', '5', 'all'])
group.add_argument('--inc20nt', help='run the incremental EPS synthesis with a library of 20 elements'
                                     'WITHOUT types and user hints.',
                   choices=['1', '2', '3', '4', '5', 'all'])
group.add_argument('--inc40nt', help='run the incremental EPS synthesis with a library of 40 elements'
                                     'WITHOUT types and user hints.',
                   choices=['1', '2', '3', '4', '5', 'all'])
group.add_argument('--bldc_nocost', help='run the Brushless DC motor controller synthesis.'
                                          'No cost function set.',
                   action="store_true")
group.add_argument('--bldc_comps', help='run the Brushless DC motor controller synthesis.'
                                        'Minimize number of components.',
                   action="store_true")
group.add_argument('--bldc_ports', help='run the Brushless DC motor controller synthesis.'
                                        'Minimize number of ports.',
                   action="store_true")

if __name__ == "__main__":

    args = parser.parse_args()
    run_all = False

    if args.all:
        print 'RUN ALL THE EXPERIMENTS:'
        run_all = True

    if args.eps20 in ['1', '2', '3', '4', '5', '6', '7', '8', '9']:
        print 'Running EPS test in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec ' \
              'with library of 20 elements...\n' % args.eps20
        pytest.main(['--lib2', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec' % args.eps20])
    if args.eps20 == 'all' or run_all:
        print 'Running 9 EPS tests in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_* with library of 20 elements...\n'
        pytest.main(['--lib2', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_6_10_dc_', 'pyco/tests/test_eps_facs.py'])

    if args.eps40 in ['1', '2', '3', '4', '5', '6', '7', '8', '9']:
        print 'Running EPS test in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec ' \
              'with library of 40 elements...\n' % args.eps40
        pytest.main(['--lib4', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec' % args.eps40])
    if args.eps40 == 'all' or run_all:
        print 'Running 9 EPS tests in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_* with library of 40 elements...\n'
        pytest.main(['--lib4', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_6_10_dc_', 'pyco/tests/test_eps_facs.py'])

    if args.eps20_ports in ['1', '2', '3', '4', '5', '6', '7', '8', '9']:
        print 'Running EPS test in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec ' \
              'with library of 20 elements. Minimize number of ports...\n' % args.eps20_ports
        pytest.main(['--lib2', '--ports', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec' % args.eps20_ports])
    if args.eps20_ports == 'all' or run_all:
        print 'Running 9 EPS tests in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_* ' \
              'with library of 20 elements. Minimize number of ports...\n'
        pytest.main(['--lib2', '--ports', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_6_10_dc_', 'pyco/tests/test_eps_facs.py'])

    if args.eps40_ports in ['1', '2', '3', '4', '5', '6', '7', '8', '9']:
        print 'Running EPS test in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec ' \
              'with library of 40 elements. Minimize number of ports...\n' % args.eps40_ports
        pytest.main(['--lib4', '--ports', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec' % args.eps40_ports])
    if args.eps40_ports == 'all' or run_all:
        print 'Running 9 EPS tests in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_* ' \
              'with library of 40 elements. Minimize number of ports...\n'
        pytest.main(['--lib4', '--ports', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_6_10_dc_', 'pyco/tests/test_eps_facs.py'])

    if args.eps20_comps in ['1', '2', '3', '4', '5', '6', '7', '8', '9']:
        print 'Running EPS test in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec ' \
              'with library of 20 elements. Minimize number of components...\n' % args.eps20_comps
        pytest.main(['--lib2', '--comps', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec' % args.eps20_comps])
    if args.eps20_comps == 'all' or run_all:
        print 'Running 9 EPS tests in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_* ' \
              'with library of 20 elements. Minimize number of components...\n'
        pytest.main(['--lib2', '--comps', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_6_10_dc_', 'pyco/tests/test_eps_facs.py'])

    if args.eps40_comps in ['1', '2', '3', '4', '5', '6', '7', '8', '9']:
        print 'Running EPS test in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec ' \
              'with library of 40 elements. Minimize number of components...\n' % args.eps40_comps
        pytest.main(['--lib4', '--comps', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_6_10_dc_%sspec' % args.eps40_comps])
    if args.eps40_comps == 'all' or run_all:
        print 'Running 9 EPS tests in pyco/tests/test_eps_facs.py::test_synth_6_10_dc_* ' \
              'with library of 40 elements. Minimize number of components...\n'
        pytest.main(['--lib4', '--comps', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_6_10_dc_', 'pyco/tests/test_eps_facs.py'])
    
    if args.inc20wt in ['1', '2', '3', '4', '5']:
        print 'Running EPS incremental test in pyco/tests/test_eps_facs.py::test_synth_inc_%s ' \
              'with library of 20 elements. Use types and user hints...\n' % args.inc20wt
        pytest.main(['--lib2', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_inc_%s' % args.inc20wt])
    if args.inc20wt == 'all' or run_all:
        print 'Running 5 EPS incremental tests in pyco/tests/test_eps_facs.py::test_synth_inc_* ' \
              'with library of 20 elements. ' \
              'Use types and user hints...\n'
        pytest.main(['--lib2', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_inc_', 'pyco/tests/test_eps_facs.py'])

    if args.inc20nt in ['1', '2', '3', '4', '5']:
        print 'Running EPS incremental test in pyco/tests/test_eps_facs.py::test_synth_inc_%s ' \
              'with library of 20 elements. WITHOUT types and user hints...\n' % args.inc20nt
        pytest.main(['--lib2', '--nt', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_inc_%s' % args.inc20nt])
    if args.inc20nt == 'all' or run_all:
        print 'Running 5 EPS incremental tests in pyco/tests/test_eps_facs.py::test_synth_inc_* ' \
              'with library of 20 elements. ' \
              'WITHOUT types and user hints...\n'
        pytest.main(['--lib2', '--nt', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_inc_', 'pyco/tests/test_eps_facs.py'])

    if args.inc40wt in ['1', '2', '3', '4', '5']:
        print 'Running EPS incremental test in pyco/tests/test_eps_facs.py::test_synth_inc_%s ' \
              'with library of 40 elements. Use types and user hints...\n' % args.inc40wt
        pytest.main(['--lib4', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_inc_%s' % args.inc40wt])
    if args.inc40wt == 'all' or run_all:
        print 'Running 5 EPS incremental tests in pyco/tests/test_eps_facs.py::test_synth_inc_* ' \
              'with library of 40 elements. ' \
              'Use types and user hints...\n'
        pytest.main(['--lib4', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_inc_', 'pyco/tests/test_eps_facs.py'])

    if args.inc40nt in ['1', '2', '3', '4', '5']:
        print 'Running EPS incremental test in pyco/tests/test_eps_facs.py::test_synth_inc_%s ' \
              'with library of 40 elements. WITHOUT types and user hints...\n' % args.inc40nt
        pytest.main(['--lib4', '--nt', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_eps_facs.py::test_synth_inc_%s' % args.inc40nt])
    if args.inc40nt == 'all' or run_all:
        print 'Running 5 EPS incremental tests in pyco/tests/test_eps_facs.py::test_synth_inc_* ' \
              'with library of 40 elements. ' \
              'WITHOUT types and user hints...\n'
        pytest.main(['--lib4', '--nt', '--timeout='+str(TIMEOUT_SEC), '-s', '-k test_synth_inc_', 'pyco/tests/test_eps_facs.py'])

    if args.bldc_nocost or run_all:
        print 'Run the Brushless DC motor controller synthesis tests in pyco/tests/test_edg_motor.py::test_ltl_spec_med. ' \
              'No cost function set...\n'
        pytest.main(['--lib3', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_edg_motor.py::test_ltl_spec_med'])

    if args.bldc_comps or run_all:
        print 'Run the Brushless DC motor controller synthesis tests in pyco/tests/test_edg_motor.py::test_ltl_spec_med. ' \
              'Minimize number of components...\n'
        pytest.main(['--lib3', '--comps', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_edg_motor.py::test_ltl_spec_med'])

    if args.bldc_ports or run_all:
        print 'Run the Brushless DC motor controller synthesis tests in pyco/tests/test_edg_motor.py::test_ltl_spec_med. ' \
              'Minimize number of ports...\n'
        pytest.main(['--lib3', '--ports', '--timeout='+str(TIMEOUT_SEC), '-s', 'pyco/tests/test_edg_motor.py::test_ltl_spec_med'])



