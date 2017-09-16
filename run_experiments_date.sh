#!/bin/bash

#stop in case of errors
set -e

#visualize with
# tail -n -1 test_synth_6_10_dc_3_* | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'

EPS_TEST_20=false
EPS_TEST_40=false
EPS_TEST_20_PLAIN=true
EPS_TEST_40_PLAIN=false

START=1
REPS=10
SPEC_INIT=6
SPEC_STOP=9

IS_CONCURRENT=false

AMP='&'
if ! $IS_CONCURRENT
then
  AMP=''
fi


if $EPS_TEST_20 || $EPS_TEST_40
then
  for ((exp=$SPEC_INIT; exp<=$SPEC_STOP; exp++))
  do
    if $EPS_TEST_20
    then
      rm -f test_synth_6_10_dc_${exp}_lib20_*
    fi
    if $EPS_TEST_40_PLAIN
    then
      rm -f test_synth_6_10_dc_${exp}_lib40_*
    fi

    for (( i=$START; i<=$REPS; i++ ))
    do
      if $EPS_TEST_20
      then
        eval "py.test --lib2 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_${exp}_lib20_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40
      then
        eval "py.test --lib4 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_${exp}_lib40_${i} 2>&1" $AMP
      fi
    done
  done
fi

if $EPS_TEST_20_PLAIN || $EPS_TEST_40_PLAIN
then
  for ((exp=$SPEC_INIT; exp<=$SPEC_STOP; exp++))
  do
    if $EPS_TEST_20_PLAIN
    then
      rm -f test_synth_6_10_dc_${exp}_plain_lib20_*
    fi
    if $EPS_TEST_40_PLAIN
    then
      rm -f test_synth_6_10_dc_${exp}_plain_lib40_*
    fi

    for (( i=$START; i<=$REPS; i++ ))
    do
      if $EPS_TEST_20_PLAIN
      then
        eval "py.test --lib2 --plain --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_${exp}_plain_lib20_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40_PLAIN
      then
        eval "py.test --lib4 --plain --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_${exp}_plain_lib40_${i} 2>&1" $AMP
      fi
    done
  done
fi
