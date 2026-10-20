#!/usr/bin/env python3
"""Ask Jev (TypeSafe System One) the textbook-audit questions about every Lib file.

State per file is assembled by code (path, module docstring, preamble, statement heads, counted
facts); Jev returns one Choice (the A–D verdict of RUBRIC.md), five yes/no judgments and one
ordered Score. Results go to results.jsonl, one line per file, written as each answer arrives.
Key: ~/.ssh/jev.key (never printed, never stored in the repo).
"""
import json, os, re, sys, time, urllib.request, urllib.error, concurrent.futures as cf
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results.jsonl')
KEY = open(os.path.expanduser('~/.ssh/jev.key')).read().strip()
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:public |private |protected |noncomputable |nonrec |scoped |unsafe )*(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque)\b')
VOCAB = ['Mathoverflow1973', 'W4W1', 'SixSphere', 'Threefold', 'Center', 'native', 'mo1973', 'finrank ℝ E = 6', 'Hemisphere.Sphere', 'lane', 'TEXTBOOK.md']

def statements(lines):
    out = []
    for i, l in enumerate(lines):
        if DECL.match(l):
            s = l.strip(); j = i + 1
            while ':=' not in s and j < len(lines) and j < i + 12 and not lines[j].startswith('theorem'):
                s += ' ' + lines[j].strip(); j += 1
            s = s.split(':=')[0].strip()
            out.append(f'l.{i+1} ' + s[:300])
    return out

def documented(lines):
    n = d = 0
    for i, l in enumerate(lines):
        if DECL.match(l) and not l.startswith('private'):
            n += 1
            k = i - 1
            while k >= 0 and (lines[k].startswith('@[') or lines[k].strip() == ''): k -= 1
            if k >= 0 and (lines[k].rstrip().endswith('-/') ): d += 1
    return d, n

def state_of(path):
    text = open(os.path.join(ROOT, path), encoding='utf-8').read()
    lines = text.split('\n')
    m = re.search(r'/-!(.*?)-/', text, re.S)
    doc = (m.group(1).strip() if m else '')[:2500]
    pre = [l for l in lines[:80] if re.match(r'^(import|public import|module|set_option|open |universe|local notation|local infix|attribute)', l)]
    st = statements(lines)
    sampled = False
    if len(st) > 120:
        step = len(st) / 120; st = [st[int(i * step)] for i in range(120)]; sampled = True
    d, n = documented(lines)
    facts = {
        'lines': len(lines), 'declarations': n, 'documented_declarations': d,
        'statements_sampled': sampled,
        'vocabulary_counts': {v: text.count(v) for v in VOCAB if text.count(v)},
        'moved_verbatim_note': bool(re.search(r'[Mm]oved verbatim', text)),
        'imports_all_of_mathlib': any(l.strip() in ('import Mathlib', 'public import Mathlib') for l in pre),
        'namespaces': sorted(set(re.findall(r'^namespace (\S+)', text, re.M)))[:20],
    }
    return {'path': path, 'directory': os.path.dirname(path), 'module_docstring': doc or '(none)',
            'preamble': pre[:40], 'statements': st, 'facts': facts}

RUBRIC = {
    'A': 'textbook-ready: generic statements, standard names, docstrings present, no project residue; could be proposed to Mathlib as is',
    'B': 'minor: only docs or names need work (stale sentences, missing docstrings, a nonstandard name, unused preamble, an ad-hoc constant)',
    'C': 'project residue in the mathematics: statements specialised to the project\'s objects, ring, universe or dimension where the textbook argument is general; project vocabulary in names or hypotheses; lemmas that exist only to feed one proof step; two unrelated topics in one file',
    'D': 'not library material: proof-specific to the project (belongs in the proof tree), or the main statement is a special case a general library (Mathlib) already has',
}
QUESTIONS = {
    'verdict': {'type': 'choice', 'instructions': 'This is evidence about one Lean 4 file of a mathematics library extracted from a research proof. Judge how ready the file is for a general library (Mathlib style), using the rubric in the criteria.', 'criteria': RUBRIC},
    'residue': {'type': 'noul', 'instructions': 'Do the statements (not the proofs) carry project-specific data: a fixed dimension such as `finrank ℝ E = 6`, names or hypotheses that refer to the project\'s own objects (Mathoverflow1973, W4W1, SixSphere, Center, Threefold, "native"), or generated names with a `_mo1973_` suffix?', 'criteria': {'true': 'yes, some statements are specialised to the project', 'false': 'no, the statements are general'}},
    'docs_stale': {'type': 'noul', 'instructions': 'Does the module docstring describe or promise declarations that are not among the file\'s statements?', 'criteria': {'true': 'the docstring names results the file does not contain', 'false': 'the docstring matches the file'}},
    'multi_topic': {'type': 'noul', 'instructions': 'Does the file mix two or more unrelated mathematical topics that a library would keep in separate files?'},
    'mathlib_has': {'type': 'noul', 'instructions': 'Is the file\'s main result something a general mathematics library such as Mathlib already provides, so that the file would be redundant there?'},
    'pinned': {'type': 'noul', 'instructions': 'Are the statements pinned to a specific ring, universe level or dimension (for example `ModuleCat.{0} ℤ`, `AddCommGrpCat.{0}`, `TopCat.{0}`, `X : Type` rather than `Type*`) where the textbook argument works in general?'},
    'readiness': {'type': 'score', 'instructions': 'How much work separates this file from a library-ready file?', 'criteria': ['none: ready as is', 'documentation and naming only', 'the statements themselves must be generalised or cleaned of project data', 'the file does not belong in a library']},
}

def ask(state):
    body = json.dumps({'state': state, 'model': 'jev-latest', 'questions': QUESTIONS}).encode()
    for attempt in range(6):
        req = urllib.request.Request('https://api.typesafe.ai/v1/systemone', data=body, headers={'Authorization': 'Bearer ' + KEY, 'Content-Type': 'application/json'})
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                return json.load(r)
        except urllib.error.HTTPError as e:
            if e.code in (429, 529): time.sleep(2 ** attempt); continue
            return {'error': e.code, 'body': e.read().decode()[:500]}
        except Exception as e:
            time.sleep(2 ** attempt); last = str(e)
    return {'error': 'retries', 'body': last}

def main():
    files = [l.strip() for g in sorted(os.listdir(os.path.dirname(OUT) + '/..')) if g.startswith('group-') and g.endswith('.txt') for l in open(os.path.join(os.path.dirname(OUT), '..', g)) if l.strip()]
    done = set()
    if os.path.exists(OUT):
        done = {json.loads(l)['path'] for l in open(OUT) if l.strip()}
    todo = [f for f in files if f not in done]
    print(f'{len(files)} files, {len(done)} done, {len(todo)} to do', flush=True)
    out = open(OUT, 'a')
    def work(f):
        st = state_of(f); r = ask(st)
        return f, st['facts'], r
    with cf.ThreadPoolExecutor(4) as ex:
        for f, facts, r in ex.map(work, todo):
            out.write(json.dumps({'path': f, 'facts': facts, 'response': r}) + '\n'); out.flush()
            a = r.get('answers', {})
            print(f, a.get('verdict', {}).get('choice', r.get('error')), flush=True)
    print('done', flush=True)

if __name__ == '__main__':
    main()
