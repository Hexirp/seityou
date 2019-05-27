#!/bin/bash

# 私の環境に固有の設定であるが、めんどくさいため消さない
COQ_PATH=/c/coq

PATH=$COQ_PATH/bin:$PATH

coqc -nois -verbose \
 -R theories/ Seityou \
 theories/Basis.v \
 theories/Path.v \
 theories/Homotopy.v \
 theories/Pwpath.v \
 theories/Contraction.v \
 theories/Peano.v \
 theories/Decidability.v \
 theories/Relation.v \
 theories/WellFoundness.v \
 theories/Equivalence.v
