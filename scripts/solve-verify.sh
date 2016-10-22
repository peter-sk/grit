#!/bin/bash
BIN=./bin
echo RUNNING LINGELING TO OBTAIN RUP PROOF
if time $BIN/lingeling $1 | grep -v "^[cs]" > $1.rup
then
  echo RUNNIGN MODIFIED DRAT-TRIM TO OBTAIN TRIG PROOF
  time $BIN/drat-trim $1 $1.rup -r $1.trig -t 86400
  echo REVERSING TRIG FILE INTO GRIT FILE
  time tac $1.trig > $1.grit
  echo RUNNING C CHECKER
  time $BIN/c-checker $1.grit
  echo RUNNING CERTIFIED CHECKER
  time $BIN/certified-checker $1 $1.grit
fi
