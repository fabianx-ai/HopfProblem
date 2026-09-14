import json, re, subprocess, sys
from pathlib import Path
DECL = re.compile(r"^(?:noncomputable |private |protected )?(?:theorem|def|abbrev|lemma|instance|structure|inductive|class) ([^\s:;(){}\[\],`\"']+)")
W = Path('Lib/Topology/MappingTorus/Wang.lean')
b = json.load(open('/tmp/wang_blocks.json'))

FAMILY_REWRITES = [
    ('FirstHurewicz.', 'SingularChains.'),
    ('PeriodTorusHigherHomology.CircleTopology.', 'SingularHomology.CircleTopology.'),
]
QUALIFY = {
    'crossProductHomology': 'SingularHomology.crossProductHomology',
    'connectingHomomorphism_cycleClass': 'SingularHomology.connectingHomomorphism_cycleClass',
    'cylinderPuncture': 'PassageHomology.cylinderPuncture',
    'linkingSphere': 'PassageHomology.linkingSphere',
    'puncturedVectorSpace': 'PassageHomology.puncturedVectorSpace',
    'puncturedCylinderHomeomorph': 'PassageHomology.puncturedCylinderHomeomorph',
    'radialCylinderDiffeomorph': 'PassageHomology.radialCylinderDiffeomorph',
    'crossProductEdge_boundary': 'SingularHomology.crossProductEdge_boundary',
    'crossProductEdge_boundary_zero': 'SingularHomology.crossProductEdge_boundary_zero',
    'crossProductZeroLeft': 'SingularHomology.crossProductZeroLeft',
    'crossProductZeroLeft_simplex_left': 'SingularHomology.crossProductZeroLeft_simplex_left',
    'homotopy_homologyMap': 'SingularHomology.homotopy_homologyMap',
    'singularHomologyMap_comp': 'SingularHomology.singularHomologyMap_comp',
    'crossProductEdge': 'SingularHomology.crossProductEdge',
    'crossInsertLeft': 'SingularHomology.crossInsertLeft',
    'crossInsertRight': 'SingularHomology.crossInsertRight',
    'biprodElement_mo1973_12801': 'PeriodTorusHigherHomology.biprodElement_mo1973_12801',
    'biprodElement_desc_mo1973_12803': 'PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803',
    'biprodElement_desc_mo1973_12803': 'PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803',
    'biprod_lift_eq_boundary_mo1973_12805': 'PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805',
    'biprod_lift_f_apply_mo1973_12802': 'PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802',
    'biprodElement_boundary_mo1973_12804': 'PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804',
    'sum_range_shift_of_endpoints_mo1973_27356': 'MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356',
}
FAMILY_REWRITES += [
    ('PeriodTorusHigherHomology.homotopy_homologyMap', 'SingularHomology.homotopy_homologyMap'),
    ('PeriodTorusHigherHomology.singularHomologyMap_comp', 'SingularHomology.singularHomologyMap_comp'),
    ('PeriodTorusHigherHomology.singularHomologyMap_id', 'SingularHomology.singularHomologyMap_id'),
]
def rewrite(text):
    for old, new in FAMILY_REWRITES:
        text = text.replace(old, new)
    for bare, full in sorted(QUALIFY.items(), key=lambda kv: -len(kv[0])):
        text = re.sub(r'(?<![A-Za-z0-9_.\'])'+re.escape(bare)+r'(?![A-Za-z0-9_.\'])', full, text)
    return text

# topo order by internal references
names = set(b.keys())
ID = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
refs = {}
for n, v in b.items():
    text = rewrite('\n'.join(v['lines']))
    cands = set()
    for m in ID.finditer(text):
        parts = m.group(0).split('.')
        for k in range(1, len(parts)+1):
            cands.add('.'.join(parts[:k]))
    # single-token (bare sibling) references: token == some row's last component (unique)
    lasts = {}
    for m in set(b):
        lasts.setdefault(m.rsplit('.', 1)[-1], []).append(m)
    bare_toks = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text))
    for tok in bare_toks:
        if len(tok) > 6 and tok in lasts and len(lasts[tok]) == 1:
            cands.add(lasts[tok][0])
    refs[n] = {c for c in cands if c in names and c != n}
idx = {n: i for i, n in enumerate(b)}
PINS = [('PeriodTorusHigherHomology.CirclePaths.circleTranslation_apply', 'PeriodTorusHigherHomology.CirclePaths.circleTranslationHomotopy'),
        ('PeriodTorusHigherHomology.CirclePaths.circleTranslation_apply', 'MappingTorusHomology.Covering.translatedPositiveLoop'),
]
for a, c in PINS:
    if a in b and c in b and a not in refs[c]:
        refs[c].add(a)
indeg = {n: len(refs[n]) for n in b}
dependents = {n: [] for n in b}
for n, ds in refs.items():
    for d in ds: dependents[d].append(n)
ready = sorted([n for n in b if indeg[n] == 0], key=lambda n: idx[n])
res = []
while ready:
    n = ready.pop(0); res.append(n)
    for m in dependents[n]:
        indeg[m] -= 1
        if indeg[m] == 0: ready.append(m)
    ready.sort(key=lambda x: idx[x])
if len(res) != len(b):
    print('CYCLE', set(b) - set(res)); sys.exit(1)

HDR = Path('/tmp/wang_header.txt').read_text()
def strip_trailing_attrs(ls):
    ls = list(ls)
    while ls and (ls[-1].strip().startswith('@[') or ls[-1].strip() == ''):
        if ls[-1].strip() == '':
            ls.pop()
        else:
            ls.pop()
            while ls and ls[-1].strip().startswith('@['):
                ls.pop()
    return ls
body = [rewrite('\n'.join(strip_trailing_attrs(b[n]['lines']))) for n in res]
body = [t.replace('def PeriodTorusHigherHomology.biprodElement_mo1973_12801', 'def PeriodTorusHigherHomology.biprodElement_mo1973_12801')
          .replace('theorem MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356', 'theorem MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356')
          .replace('theorem PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803', 'def PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803')
          .replace('theorem PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805', 'theorem PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805')
          .replace('theorem PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802', 'theorem PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802')
          .replace('theorem PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804', 'theorem PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804') for t in body]
W.write_text(HDR + '\n\n'.join(body) + '\n\nend Mathoverflow1973\n')
out = subprocess.run(['lake','build','Lib'], capture_output=True, text=True, cwd='/home/glm/hopf').stdout
errs = [l for l in out.split('\n') if l.startswith('error:')]
print('rows:', len(b), '| order ok | errs:', len(errs))
for e in errs[:12]: print(' ', e[:140])
