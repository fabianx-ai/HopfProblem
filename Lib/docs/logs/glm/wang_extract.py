import json, re, subprocess
from pathlib import Path
DECL = re.compile(r"^(?:noncomputable |private |protected )?(?:theorem|def|abbrev|lemma|instance|structure|inductive|class) ([^\s:;(){}\[\],`\"']+)")
def upwalk(lines, i):
    a = i
    while a > 0:
        if lines[a-1].strip() == '':
            a -= 1; continue
        tt = lines[a-1].strip()
        if (tt.startswith('attribute ') or tt.startswith('set_option ')) and tt.endswith(' in'):
            a -= 1; continue
        if tt.startswith('@['):
            a -= 1; continue
        if tt.endswith('-/'):
            k = a - 1
            if not tt.startswith('/--'):
                while k > 0 and not lines[k-1].lstrip().startswith('/--'):
                    k -= 1
            a = k; continue
        break
    return a
def extract(bare, files=None):
    out = subprocess.run(['grep','-rln','--include=*.lean','--exclude-dir=Proof'] + (files or []) + [bare, 'Hopf/'], capture_output=True, text=True).stdout.strip()
    for f in [x for x in out.split('\n') if x]:
        lines = Path(f).read_text().split('\n')
        for i, l in enumerate(lines):
            m = DECL.match(l)
            if m and m.group(1) == bare:
                a = upwalk(lines, i)
                end = i + 1
                while end < len(lines):
                    l2 = lines[end]
                    if DECL.match(l2) and not l2.startswith((' ', '\t')):
                        break
                    if l2.strip() == 'end Mathoverflow1973':
                        break
                    end += 1
                return {'file': f, 'lines': lines[a:end], 'declline': i}
    return None
if __name__ == '__main__':
    d = json.load(open('Lib/reports/I-wang-dependencies.json'))
    b = {}
    for r in d['declarations']:
        bare = r['name'].replace('Mathoverflow1973.', '', 1)
        v = extract(bare)
        if v: b[bare] = v
    # extra closure rows discovered by build (not in the JSON's 232)
    for bare in ['PeriodTorusHigherHomology.biprodElement_mo1973_12801',
                 'PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802',
                 'PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803',
                 'PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804',
                 'PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805',
                 'MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356',
                 'PeriodTorusHigherHomology.CirclePaths.circleTranslation_apply']:
        v = extract(bare)
        if v: b[bare] = v; b[bare]['extra'] = True
        else: print('MISSING', bare)
    json.dump(b, open('/tmp/wang_blocks.json','w'))
    print('rows:', len(b))
