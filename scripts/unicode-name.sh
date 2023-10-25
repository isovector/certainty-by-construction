#! /usr/bin/env bash

cat $1 | uniname -bcpuge | tail -n2 | head -n1
