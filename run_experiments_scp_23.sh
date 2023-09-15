#!/bin/bash

# stop in case of errors
set -e

# visualize with
# tail -n -1 test_synth_6_10_dc_3_* | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'
# to get number at minus nth line, use
# read_minus_nth_line.sh 5 workspace/pyco/test_edg_motor_lib16_*

# IMPORTANT
# in this tests, the library was verified for determininsm beforehand,
# thus, in the tests definitions the line
# library.verify_determinism(stop_if_fails=True)
# was commented out, meaning that the check was not repeated for each experiment

EDG_MOTOR_TEST_16=false
EDG_MOTOR_TEST_24=false
EDG_MOTOR_TEST_32=false
EPS_TEST_20=false
EPS_TEST_40=false
EPS_TEST_20_PLAIN=false
EPS_TEST_40_PLAIN=true
SPI_PLAIN=false
SPI_SD=false

IS_CONCURRENT=false

START=1
REPS=1
SPEC_INIT=9
SPEC_STOP=9

AMP='&'
if ! $IS_CONCURRENT
then
  AMP=''
fi

if $SPI_PLAIN
then
  rm -f test_adc_int_*
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc2_int) >> scp_test_adc_int_2 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc3_int) >> scp_test_adc_int_3 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc4_int) >> scp_test_adc_int_4 2>&1" $AMP
fi

if $SPI_SD
then
  rm -f test_adc_sd_int_*
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc2_int_sd) >> scp_test_adc_sd_int_2 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc3_int_sd) >> scp_test_adc_sd_int_3 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc3_int_sd) >> scp_test_adc_sd_int_3 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc3_int_sd) >> scp_test_adc_sd_int_3 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc4_int_sd) >> scp_test_adc_sd_int_4 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc5_int_sd) >> scp_test_adc_sd_int_5 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc6_int_sd) >> scp_test_adc_sd_int_6 2>&1" $AMP
  eval "(date; py.test --timeout=1000 -s pyco/tests/test_spi.py::test_adc8_int_sd) >> scp_test_adc_sd_int_8 2>&1" $AMP
fi


if $EDG_MOTOR_TEST
then
  for (( i=$START; i<=$REPS; i++ ))
  do
    if $EDG_MOTOR_TEST_16
    then
      rm -f time_test_edg_motor_lib16_${i}
      eval "(date; py.test --lib2 --timeout=1000 -s pyco/tests/test_edg_motor.py::test_ltl_spec_med) >> scp_test_edg_motor_lib16_${i} 2>&1" $AMP
    fi
    if $EDG_MOTOR_TEST_24
    then
      rm -f time_test_edg_motor_lib24_${i}
      eval "py.test --lib3 --timeout=1000 -s pyco/tests/test_edg_motor.py::test_ltl_spec_med) >> scp_test_edg_motor_lib24_${i} 2>&1" $AMP
    fi
    if $EDG_MOTOR_TEST_32
    then
      rm -f time_test_edg_motor_lib32_${i}
      eval "(date; py.test --lib4 --timeout=1000 -s pyco/tests/test_edg_motor.py::test_ltl_spec_med) >> scp_test_edg_motor_lib32_${i} 2>&1" $AMP
    fi

   done
fi

if $EPS_TEST_20 || $EPS_TEST_40
then
  for ((exp=$SPEC_INIT; exp<=$SPEC_STOP; exp++))
  do
    if $EPS_TEST_20
    then
      rm -f scp_test_synth_6_10_dc_${exp}_lib20_*
    fi
    if $EPS_TEST_40_PLAIN
    then
      rm -f scp_test_synth_6_10_dc_${exp}_lib40_*
    fi

    for (( i=$START; i<=$REPS; i++ ))
    do
      if $EPS_TEST_20
      then
        eval "(date; py.test --lib2 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec) >> scp_test_synth_6_10_dc_${exp}_lib20_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40
      then
        eval "(date; py.test --lib4 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec) >> scp_test_synth_6_10_dc_${exp}_lib40_${i} 2>&1" $AMP
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
      rm -f scp_test_synth_6_10_dc_${exp}_plain_lib20_*
    fi
    if $EPS_TEST_40_PLAIN
    then
      rm -f scp_test_synth_6_10_dc_${exp}_plain_lib40_*
    fi

    for (( i=$START; i<=$REPS; i++ ))
    do
      if $EPS_TEST_20_PLAIN
      then
        eval "(date; py.test --lib2 --plain --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec) >> scp_test_synth_6_10_dc_${exp}_plain_lib20_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40_PLAIN
      then
        eval "(date; py.test --lib4 --plain --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec) >> scp_test_synth_6_10_dc_${exp}_plain_lib40_${i} 2>&1" $AMP
      fi
    done
  done
fi

