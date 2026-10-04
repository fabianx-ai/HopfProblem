"""Import graph of the worktree (project files + Mathlib/other package sources)."""
import os, re, json, functools
ROOT = '/home/goblin/hopf-facades'
PKG = os.path.join(ROOT, '.lake/packages')
IMP = re.compile(r'^(public\s+)?(meta\s+)?import\s+(\S+)', re.M)

def strip_comments(s):
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    return re.sub(r'--.*', '', s)

def parse(path):
    s = open(path, encoding='utf-8').read()
    t = strip_comments(s)
    is_module = re.search(r'^module\s*$', t, re.M) is not None
    imps = [(m.group(3), bool(m.group(1)), bool(m.group(2))) for m in IMP.finditer(t)]
    return is_module, imps

def modname(rel):
    return rel[:-5].replace('/', '.')

@functools.lru_cache(None)
def project_files():
    out = {}
    for d, ds, fs in os.walk(ROOT):
        if '/.lake' in d or '/.git' in d: continue
        for f in fs:
            if f.endswith('.lean'):
                rel = os.path.relpath(os.path.join(d, f), ROOT)
                out[modname(rel)] = rel
    return out

def find_pkg(mod):
    rel = mod.replace('.', '/') + '.lean'
    for p in os.listdir(PKG):
        q = os.path.join(PKG, p, rel)
        if os.path.exists(q): return q
    return None

class Graph:
    def __init__(self):
        self.info = {}  # mod -> (is_module, [(imp, public, meta)])
        self.files = project_files()
    def get(self, m):
        if m not in self.info:
            if m in self.files: p = os.path.join(ROOT, self.files[m])
            else: p = find_pkg(m)
            self.info[m] = parse(p) if p else (True, [])
        return self.info[m]
    def imports(self, m): return [i for i, _, _ in self.get(m)[1]]
    def closure(self, roots):
        seen = set(); st = list(roots)
        while st:
            x = st.pop()
            if x in seen: continue
            seen.add(x); st.extend(self.imports(x))
        return seen
