#!/bin/bash
S=/home/goblin/.claude/jobs/06995e68/tmp/wave2/cube3
W=/home/goblin/hopf-w2-cube3
cd $W
python3 - <<'PY'
import json
S='/home/goblin/.claude/jobs/06995e68/tmp/wave2/cube3/'
pc=json.load(open(S+'piece_of.json'))
for p in sorted(set(pc.values())):
    open(S+'split/stay_'+p+'.txt','w').write('\n'.join(n for n,q in pc.items() if q!=p)+'\n')
PY
for P in Lattice Cells Faces Coverage RelInterior SquareBoundary Separation; do
  python3 /home/goblin/lean-agent-ide/tools/split_module.py --dump /home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl \
    --module Lib.Topology.Dimension.CubeBoundaryThreeCells --source $1 \
    --stay $S/split/stay_$P.txt --keep-out $S/split/keep_$P.lean --move-out $S/split/$P.raw.lean \
    --receipt $S/split/split-$P.receipt.json || echo "FAIL $P"
done
echo "done $?"
