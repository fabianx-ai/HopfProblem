import json,subprocess,sys,os
S='/home/goblin/.claude/jobs/06995e68/tmp/wave2/transversality'
D='/home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl'
MOD='Lib.Geometry.Manifold.Transversality.Basic'
W='/home/goblin/hopf-w2-transversality'
SRC=S+'/Basic.orig.lean'
rows=[json.loads(l) for l in open(D)]
mine={r['name']:r for r in rows if r['module']==MOD and r.get('range')}
start={n:r['range'][0] for n,r in mine.items()}
def by_lines(a,b): return {n for n,l in start.items() if a<=l<=b}
P={}
P['Diffeomorph']={"Diffeomorph.toPartialDiffeomorph'","IsLocalDiffeomorph.diffeomorph'"}
P['RegularValues']=by_lines(123,295)
P['Transverse']=by_lines(324,704)-{'TransverseCoordinates.exists_null_exceptional_native_translations','TransverseCoordinates.dense_native_translations'}|{'ContinuousLinearMap.surjective_coprod_comp_left'}
P['Parametric']={'TransverseCoordinates.exists_null_exceptional_native_translations','TransverseCoordinates.dense_native_translations'}
P['MorseBelt']=by_lines(751,1147)
P['CenteredChart']=by_lines(1174,1214)
P['SupportedIsotopy']=by_lines(1221,1490)|{'SupportedDiffeomorph.exists_supported_isotopy_extension','SupportedDiffeomorph.IsotopicToIdentity.symm'}
P['LinearFramePaths']={n for n in start if n.startswith('LinearFramePaths.')}
P['GermLinearization']={n for n in start if n.startswith('SmallPerturbation.')}
P['GermRealization']={n for n in start if n.startswith('SupportedGerms.')}-{'SupportedGerms.exists_disk_chart_isotopy'}
P['DiskShrinking']={n for n in start if n.startswith('SmoothRadial.')}|by_lines(2710,2824)
P['DiscTheorem']={'DiskShrinking.exists_larger_closedBall_subset','DiskShrinking.exists_disk_ellipsoid_in_open','DiskShrinking.exists_chart_disk_shrinking','SupportedGerms.exists_disk_chart_isotopy','DiskShrinking.exists_embedded_disk_isotopy_of_same_center'}
P['Homogeneity']={'SupportedDiffeomorph.exists_supported_pointMoving','SupportedDiffeomorph.exists_open_pointMoving'}
allp=[n for s in P.values() for n in s]
assert len(allp)==len(set(allp))==len(mine), (len(allp),len(set(allp)),len(mine), set(mine)-set(allp))
if __name__=='__main__':
    for k,v in P.items(): print(k,len(v))
    if len(sys.argv)>1 and sys.argv[1]=='run':
        for k,v in P.items():
            stay=S+f'/stay_{k}.txt'
            open(stay,'w').write('\n'.join(sorted(set(mine)-v))+'\n')
            out=f'{W}/Lib/Geometry/Manifold/Transversality/{k}.lean'
            r=subprocess.run(['python3','/home/goblin/lean-agent-ide/tools/split_module.py','--dump',D,'--module',MOD,'--source',SRC,'--stay',stay,'--keep-out',S+f'/keep_{k}.lean','--move-out',out,'--receipt',S+f'/split_{k}.json'],capture_output=True,text=True)
            print(k,r.returncode,r.stdout[-300:],r.stderr[-500:])
