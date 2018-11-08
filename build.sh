#!/bin/bash

# Hexirpの環境に固有の設定であるが、めんどくさいため消さない
COQ_PATH=/c/coq

PATH=$COQ_PATH/bin:$PATH

coqc \
 -R theories/ Seityou \
 theories/Basis.v \
 theories/Contraction.v \
 theories/K.v \
 theories/W.v
