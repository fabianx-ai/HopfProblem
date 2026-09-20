#!/bin/bash
cd <worktree>
T=$T
LAKE=/home/goblin/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lake
echo "start $(date)" > $T/int4_dump.log
$LAKE env /home/goblin/lean-agent-ide/.lake/build/bin/lean-agent-ide dump Hopf.Proof.Final Solution Lib --modules Hopf,Lib > $T/dump_int4_raw.jsonl 2>> $T/int4_dump.log; echo "raw-exit $?" >> $T/int4_dump.log
python3 $T/int4_rename_map.py $T/dump_split.jsonl $T/dump_int4_raw.jsonl $T/int4_rename.txt >> $T/int4_dump.log 2>&1
$LAKE env /home/goblin/lean-agent-ide/.lake/build/bin/lean-agent-ide dump Hopf.Proof.Final Solution Lib --modules Hopf,Lib --rename $T/int4_rename.txt > $T/dump_int4_renamed.jsonl 2>> $T/int4_dump.log; echo "renamed-exit $?" >> $T/int4_dump.log
echo "end $(date)" >> $T/int4_dump.log
