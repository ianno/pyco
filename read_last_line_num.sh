#!/bin/bash

for i in "${@:1}"
do
  tail -n -1 "$i" | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'
done