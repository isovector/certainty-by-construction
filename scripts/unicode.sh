#! /usr/bin/env bash

cat $1 | perl -C7 -ne 'for(split(//)){print $_." ".sprintf("U+%04X", ord)."\n"}'

