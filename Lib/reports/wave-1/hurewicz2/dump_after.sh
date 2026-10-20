#!/bin/bash
cd /home/goblin/hopf-w1-hurewicz2
export LEAN_NUM_THREADS=3 GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'
S=/home/goblin/.claude/jobs/06995e68/tmp/wave1/hurewicz2
/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake env /home/goblin/lean-agent-ide/.lake/build/bin/lean-agent-ide dump Solution Lib --modules Hopf,Lib > $S/dump_after.jsonl 2> $S/dump_after.err
echo "done $?" >> $S/dump_after.err
