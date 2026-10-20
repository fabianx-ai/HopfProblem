#!/bin/bash
cd <worktree>
L=$T/int4_build2.log
LAKE=/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake
echo "start $(date)" > $L
$LAKE build Lib >> $L 2>&1; echo "lib-exit $?" >> $L
$LAKE build Solution S6Shortcuts S6 Challenge >> $L 2>&1; echo "consumers-exit $?" >> $L
echo "end $(date)" >> $L
