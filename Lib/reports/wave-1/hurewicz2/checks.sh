#!/bin/bash
cd /home/goblin/hopf-w1-hurewicz2
export LEAN_NUM_THREADS=3 GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'
L=/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake
echo "### lake build Lib"; $L build Lib; echo "step1 $?"
echo "### lake build Solution S6Shortcuts S6 Challenge"; $L build Solution S6Shortcuts S6 Challenge; echo "step2 $?"
echo "### lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit"; $L build Lib.AxiomAudit Hopf.Proof.AxiomAudit; echo "step3 $?"
echo "done 0"
