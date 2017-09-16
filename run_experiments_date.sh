#!/bin/bash

#stop in case of errors
set -e

#visualize with
# tail -n -1 test_synth_6_10_dc_3_* | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'

EPS_TEST_20=false
EPS_TEST_40=false
EPS_TEST_20_PLAIN=false
EPS_TEST_40_PLAIN=false

IS_CONCURRENT=false

AMP='&'
if ! $IS_CONCURRENT
then
  AMP=''
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

if $EPS_TEST_20_PLAIN || $EPS_TEST_40_PLAIN
then
  for exp in {1..9}
  do
    rm -f test_synth_6_10_dc_${exp}_*

    for i in {1..10}
    do
      if $EPS_TEST_20
      then
        eval "py.test --lib2 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_plain_lib20_${exp}_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40
      then
        eval "py.test --lib4 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_plain_lib40_${exp}_${i} 2>&1" $AMP
      fi
    done
  done
fi
