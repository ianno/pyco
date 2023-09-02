#!/bin/bash

for i in "${@:2}"
do
  tail -n $1 "$i" | sed -n '1p' | grep -Eo '[+-]?[0-9]+'
done