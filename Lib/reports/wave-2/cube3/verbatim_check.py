# (pieces as of the split commit 344b7b6c) every unit moved by a split run occurs verbatim (its source lines) in its piece
import json,glob,subprocess
S='/home/goblin/.claude/jobs/06995e68/tmp/wave2/cube3/split/'
W='/home/goblin/hopf-w2-cube3/Lib/Topology/Dimension/CubeBoundaryThreeCells/'
src=open(S+'source_vis.lean').read().split('\n')
tot=0;names=set()
for f in sorted(glob.glob(S+'split-*.receipt.json')):
    P=f.split('split-')[1].split('.')[0]; r=json.load(open(f)); piece=subprocess.run(['git','-C','/home/goblin/hopf-w2-cube3','show','344b7b6c:Lib/Topology/Dimension/CubeBoundaryThreeCells/'+P+'.lean'],capture_output=True,text=True,check=True).stdout
    for u in r['units']:
        if u['class']!='move': continue
        a,b=u['lines']; t='\n'.join(src[a-1:b])
        assert t in piece,(P,u['names'][:1]); tot+=1; names|=set(u['names'])
print('moved units verbatim in pieces:',tot,'names',len(names))
