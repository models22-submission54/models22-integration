#!/bin/bash

for i in 0 1 2 3 4 5 6
do
    for j in 1 2 3
    do
        echo "Running case $i - subgoal $j"
        z3 output$i-C$j.smt2
    done
done

$SHELL