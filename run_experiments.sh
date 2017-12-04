#!/bin/bash

#stop in case of errors
#set -e

#visualize with
# tail -n -1 test_synth_6_10_dc_3_* | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'

NO_COST=false
MINIMIZE_PORTS=false
MINIMIZE_COMPS=true
EDG_MOTOR_TEST=false
EPS_TEST_20=true
EPS_TEST_40=true
INCREMENTAL_EPS_TEST_20=false
INCREMENTAL_EPS_TEST_40=false
INCREMENTAL_WITH_TYPES=false
INCREMENTAL_WITHOUT_TYPES=false

IS_CONCURRENT=false

AMP='&'
if ! $IS_CONCURRENT
then
  AMP=''
fi

if $EDG_MOTOR_TEST
then
  for i in {1..100}
  do
    if $NO_COST
    then
      rm -f time_test_edg_motor_nocost_${i}
      eval "py.test --lib3 --timeout=1000 -s pyco/tests/test_edg_motor.py::test_ltl_spec_med >> test_edg_motor_nocost_${i} 2>&1" $AMP
    fi
    if $MINIMIZE_PORTS
    then  
      rm -f time_test_edg_motor_ports_${i}
      eval "py.test --lib3 --ports --timeout=1000 -s pyco/tests/test_edg_motor.py::test_ltl_spec_med >> test_edg_motor_ports_${i} 2>&1" $AMP
    fi 
    if $MINIMIZE_COMPS
    then  
      rm -f time_test_edg_motor_comps_${i}
      eval "py.test --lib3 --comps --timeout=1000 -s pyco/tests/test_edg_motor.py::test_ltl_spec_med >> test_edg_motor_comps_${i} 2>&1" $AMP
    fi
 done
fi

if $EPS_TEST_20 || $EPS_TEST_40
then
  for exp in {1..9}
  do
    if $NO_COST
    then
    rm -f test_synth_6_10_dc_nocost_${exp}_*

    for i in {1..100}
    do
      if $EPS_TEST_20
      then
        eval "py.test --lib2 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_nocost_lib20_${exp}_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40
      then
        eval "py.test --lib4 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_nocost_lib40_${exp}_${i} 2>&1" $AMP
      fi
    done
    fi
    if $MINIMIZE_PORTS
    then
    rm -f test_synth_6_10_dc_ports_${exp}_*

    for i in {1..100}
    do
      if $EPS_TEST_20
      then
        eval "py.test --lib2 --ports --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_ports_lib20_${exp}_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40
      then
        eval "py.test --lib4 --ports --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_ports_lib40_${exp}_${i} 2>&1" $AMP
      fi
    done
    fi
    if $MINIMIZE_COMPS
    then
    rm -f test_synth_6_10_dc_comps_${exp}_*

    for i in {1..100}
    do
      if $EPS_TEST_20
      then
        eval "py.test --lib2 --comps --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_comps_lib20_${exp}_${i} 2>&1" $AMP
      fi
      if $EPS_TEST_40
      then
        eval "py.test --lib4 --comps --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_6_10_dc_${exp}spec >> test_synth_6_10_dc_comps_lib40_${exp}_${i} 2>&1" $AMP
      fi
    done
    fi
  done
fi

# test on incremental number of ports
if $INCREMENTAL_EPS_TEST_20 || $INCREMENTAL_EPS_TEST_40
then
  for exp in {1..5}
  do
    rm -f test_synth_inc_${exp}_*

    for i in {1..100}
    do
      if $INCREMENTAL_EPS_TEST_20
      then
        if $INCREMENTAL_WITH_TYPES
        then
          eval "py.test --lib2 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_inc_${exp} >> test_synth_inc_lib20_${exp}_${i} 2>&1" $AMP
        fi
        if $INCREMENTAL_WITHOUT_TYPES
        then
          eval "py.test --lib2 --nt --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_inc_${exp} >> test_synth_inc_nt_lib20_${exp}_${i} 2>&1" $AMP
        fi
      fi
      if $INCREMENTAL_EPS_TEST_40
      then
        if $INCREMENTAL_WITH_TYPES
        then
          eval "py.test --lib4 --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_inc_${exp} >> test_synth_inc_lib40_${exp}_${i} 2>&1" $AMP
        fi
        if $INCREMENTAL_WITHOUT_TYPES
        then
          eval "py.test --lib4 --nt --timeout=1000 -s pyco/tests/test_eps_facs.py::test_synth_inc_${exp} >> test_synth_inc_nt_lib40_${exp}_${i} 2>&1" $AMP
        fi
      fi
    done
  done
fi
