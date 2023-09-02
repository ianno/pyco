#!/bin/bash

#stop in case of errors
set -e

#visualize with
# tail -n -1 test_synth_6_10_dc_3_* | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'

EDG_MOTOR_TEST=false
EPS_TEST_20=false
EPS_TEST_40=false
INCREMENTAL_EPS_TEST_20=false
INCREMENTAL_EPS_TEST_40=false
INCREMENTAL_WITH_TYPES=true
INCREMENTAL_WITHOUT_TYPES=false

IS_CONCURRENT=false

AMP='&'
if ! $IS_CONCURRENT
then
  AMP=''
fi


if $EDG_MOTOR_TEST
then
  for i in {1..10}
  do
    rm -f time_test_edg_motor_${i}
     eval "py.test --lib3 --timeout=1000 -s pyco/tests/test_edg_motor.py::test_ltl_spec_med >> test_edg_motor_${i} 2>&1" $AMP
  done
fi

if $EPS_TEST_20 || $EPS_TEST_40
then
  for exp in {1..9}
  do
    rm -f test_synth_6_10_dc_${exp}_*

    for i in {1..10}
    do
      if $EPS_TEST_20
      then
        eval "py.test --lib2 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_lib20_${exp}_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40
      then
        eval "py.test --lib4 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_lib40_${exp}_${i} 2>&1" $AMP
      fi
    done
  done
fi

# test on incremental number of ports
if $INCREMENTAL_EPS_TEST_20 || $INCREMENTAL_EPS_TEST_40
then
  for exp in {1..5}
  do
    rm -f test_synth_inc_${exp}_*

    for i in {1..10}
    do
      if $INCREMENTAL_EPS_TEST_20
      then
        if $INCREMENTAL_WITH_TYPES
        then
          eval "py.test --lib2 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_inc_${exp} >> test_synth_inc_lib20_${exp}_${i} 2>&1" $AMP
        fi
        if $INCREMENTAL_WITHOUT_TYPES
        then
          eval "py.test --lib2 --nt --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_inc_${exp} >> test_synth_inc_lib20_${exp}_${i} 2>&1" $AMP
        fi
      fi
      if $INCREMENTAL_EPS_TEST_40
      then
        if $INCREMENTAL_WITH_TYPES
        then
          eval "py.test --lib4 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_inc_${exp} >> test_synth_inc_lib20_${exp}_${i} 2>&1" $AMP
        fi
        if $INCREMENTAL_WITHOUT_TYPES
        then
          eval "py.test --lib4 --nt --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_inc_${exp} >> test_synth_inc_lib20_${exp}_${i} 2>&1" $AMP
        fi
      fi
    done
  done
fi
