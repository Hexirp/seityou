#!/bin/bash

# 私の環境に固有の設定であるが、めんどくさいため消さない
COQ_PATH=/c/coq

PATH=$COQ_PATH/bin:$PATH

coqide -nois -R theories/ Seityou
