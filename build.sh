#!/bin/bash

# Hexirpの環境に固有の設定であるが、めんどくさいため消さない
COQ_PATH=/c/coq

PATH=$COQ_PATH/bin:$PATH

coqc -nois \
 -R theories/ Seityou \
 theories/Basis.v \
 theories/Functional.v \
 theories/Homotopical.v \
 theories/Contraction.v \
 theories/D.v \
 theories/K.v \
 theories/W.v
