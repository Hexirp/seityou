#!/bin/bash

# Hexirpの環境に固有の設定であるが、めんどくさいため消さない
COQ_PATH=/c/coq

PATH=$COQ_PATH/bin:$PATH

coqc -nois -verbose \
 -R theories/ Seityou \
 theories/Basis.v \
 theories/Path.v \
 theories/Homotopy.v \
 theories/Pwpath.v \
 theories/Contraction.v \
 theories/Equivalence.v \
 theories/Peano.v \
 theories/Decidability.v \
 theories/Relation.v
