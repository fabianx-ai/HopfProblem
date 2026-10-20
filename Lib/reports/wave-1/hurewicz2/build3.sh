#!/bin/bash
cd /home/goblin/hopf-w1-hurewicz2
export LEAN_NUM_THREADS=3 GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'
/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake build Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition
echo "done $?"
