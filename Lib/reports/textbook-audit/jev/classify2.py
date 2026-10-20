#!/usr/bin/env python3
"""Second Jev run: ten narrow criteria per file instead of one verdict question.

Code assembles the state (as in classify.py, plus counted facts about universes, `.{0}` pins,
docstring coverage per statement); Jev answers ten judgments, each with explicit criteria; the
A–D verdict is then computed by code from the ten answers (rules in compare2.py), never asked
directly. Results: results2.jsonl.
"""
import json, os, re, sys, time, urllib.request, urllib.error, concurrent.futures as cf
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from classify import ROOT, KEY, DECL, VOCAB, statements, ask as _ask
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results2.jsonl')

def state_of(path):
    text = open(os.path.join(ROOT, path), encoding='utf-8').read(); lines = text.split('\n')
    m = re.search(r'/-!(.*?)-/', text, re.S); doc = (m.group(1).strip() if m else '')[:3000]
    pre = [l for l in lines[:80] if re.match(r'^(import|public import|module|set_option|open |universe|local notation|local infix|attribute)', l)]
    st = []; n = d = 0
    for i, l in enumerate(lines):
        if DECL.match(l) and not l.startswith('private'):
            n += 1; k = i - 1
            while k >= 0 and (lines[k].startswith('@[') or lines[k].strip() == ''): k -= 1
            has = k >= 0 and lines[k].rstrip().endswith('-/'); d += has
            s = l.strip(); j = i + 1
            while ':=' not in s and j < len(lines) and j < i + 12: s += ' ' + lines[j].strip(); j += 1
            st.append(('[doc] ' if has else '[nodoc] ') + f'l.{i+1} ' + s.split(':=')[0].strip()[:280])
    sampled = len(st) > 100
    if sampled: step = len(st) / 100; st = [st[int(i * step)] for i in range(100)]
    facts = {
        'lines': len(lines), 'public_declarations': n, 'with_docstring': d,
        'docstring_coverage_percent': round(100 * d / n) if n else None, 'statements_sampled_to_100': sampled,
        'project_vocabulary_counts': {v: text.count(v) for v in VOCAB if text.count(v)},
        'says_moved_verbatim': bool(re.search(r'[Mm]oved verbatim', text)),
        'imports_all_of_mathlib': any(l.strip() in ('import Mathlib', 'public import Mathlib') for l in pre),
        'import_count': sum(1 for l in pre if 'import' in l),
        'universe_zero_pins': len(re.findall(r'\.\{0\}', text)),
        'binders_Type_star': len(re.findall(r':\s*Type\*', text)), 'binders_Type_fixed': len(re.findall(r':\s*Type[)\s\]]', text)),
        'set_option_lines': [l for l in pre if l.startswith('set_option')],
        'namespaces': sorted(set(re.findall(r'^namespace (\S+)', text, re.M)))[:25],
        'cites_project_manuscript': bool(re.search(r'TEXTBOOK\.md|Lib/docs/[A-Z]\.md|lane [A-Z]|CD-0\d|PD-L\d|\(C\d\d\)|receipt', text)),
        'cites_textbook_or_paper': bool(re.search(r'Hatcher|Milnor|Godement|Hartshorne|Bredon|Iversen|Weibel|Spanier|Lee\b|Hirsch|Ahlfors|Kashiwara|tom Dieck|May\b|Bott|Tu\b|Guillemin|Whitney|Smale|Kervaire|Wall\b|Massey|Munkres|Rotman|Cartan|Eilenberg', text)),
    }
    return {'path': path, 'directory': os.path.dirname(path), 'module_docstring': doc or '(none)', 'preamble': pre[:40], 'statements': st, 'facts': facts}

Q = {
 'cites_textbook': {'type': 'noul', 'instructions': 'Does the module docstring name a textbook or paper source for its results (an author and a theorem, section or chapter), rather than only the project\'s own manuscripts, lanes, receipts or plan coordinates?', 'criteria': {'true': 'a standard reference such as Hatcher Thm 2.20, Milnor Morse Theory §3, Godement II.5, Hartshorne III.8 is named', 'false': 'no reference, or only project documents (CENTER_*_TEXTBOOK.md, Lib/docs/*.md, lane letters, CD-04, receipts)'}},
 'docstring_accurate': {'type': 'noul', 'instructions': 'Does the module docstring describe what the file contains? Compare the results it announces with the statements listed.', 'criteria': {'true': 'every result the docstring announces is among the statements and the docstring does not narrate a plan, another file, or history', 'false': 'it promises declarations that are not in the file, describes another file, or is mainly process narrative'}},
 'docstrings_complete': {'type': 'noul', 'instructions': 'Are the public theorems and definitions documented? Use the [doc]/[nodoc] tags on the statements and the coverage percentage in the facts.', 'criteria': {'true': 'nearly every public statement has a docstring (coverage at least 90%)', 'false': 'many public statements lack docstrings'}},
 'names_standard': {'type': 'noul', 'instructions': 'Do the names and namespaces follow Mathlib conventions and name the mathematical object (Foo.bar_of_baz, IsFoo, snake_case theorems, UpperCamelCase types), rather than a consumer, a proof phase, a lane, a generated suffix such as _mo1973_1234, or a project word such as native?', 'criteria': {'true': 'names are what a Mathlib reviewer would accept with at most a few renames', 'false': 'names encode the project, its proof steps, generated suffixes, or nonstandard casing'}},
 'generality': {'type': 'score', 'instructions': 'How general are the statements compared with the textbook version of the same results? Look at type-class assumptions, universes, the coefficient ring, dimensions and the objects in the hypotheses.', 'criteria': ['textbook generality: arbitrary types, universes, rings or dimensions as the theorem allows', 'mild pins: a fixed universe level (Type, .{0}) or ℤ coefficients where the argument is generic', 'pinned to a specific ring, dimension, index, or number of pieces where the textbook statement is general', 'pinned to the project\'s own objects: hypotheses or types that only the project instantiates']},
 'project_vocabulary': {'type': 'noul', 'instructions': 'Do the statements, hypotheses, namespaces or names refer to the project\'s own objects or vocabulary (Mathoverflow1973, W4W1, SixSphere, Center, Threefold, SpecialPeriods, "native", finrank ℝ E = 6, Hemisphere.Sphere, _mo1973_)?', 'criteria': {'true': 'yes, in at least one statement or name', 'false': 'no'}},
 'single_topic': {'type': 'noul', 'instructions': 'Is the file one coherent topic that a library would keep together in one file at this path?', 'criteria': {'true': 'one subject, one or two namespaces, a Mathlib-style location', 'false': 'several unrelated subjects, many namespaces, or helpers from other areas (real analysis under a Morse namespace, a quotient lemma in a suspension file)'}},
 'preamble_clean': {'type': 'noul', 'instructions': 'Is the preamble what a library file needs: targeted imports, no unused set_option, open scoped, universe or local notation lines? Use the preamble lines and the facts (import Mathlib, set_option lines).', 'criteria': {'true': 'targeted imports and no leftover options or notation', 'false': 'import Mathlib, set_option maxSynthPendingDepth, open scoped … Modular UpperHalfPlane, unused universe u v, local notation for slash actions'}},
 'redundant_with_mathlib': {'type': 'noul', 'instructions': 'Is the file\'s main result a special case or restatement of something Mathlib already provides under another name?', 'criteria': {'true': 'the main statement is available in Mathlib (name it mentally: Representation.dual, GroupExtension.Splitting, Presheaf.isLocallySurjective_toSheafify, Functor.rightDerivedZeroIsoSelf, Real.artanh_tanh, …)', 'false': 'the result is not in Mathlib'}},
 'proof_specific': {'type': 'noul', 'instructions': 'Does the file exist to feed one step of the project\'s proof rather than to state reusable mathematics: specific numeric constants, adapter or bridge or consumer or receipt lemmas, a fixed number of pieces or cells, hypotheses that only the project instantiates?', 'criteria': {'true': 'yes, it is a proof-specific adapter that belongs in the proof tree', 'false': 'no, it states reusable mathematics'}},
}

def ask(state):
    body = json.dumps({'state': state, 'model': 'jev-latest', 'questions': Q}).encode()
    last = ''
    for attempt in range(6):
        req = urllib.request.Request('https://api.typesafe.ai/v1/systemone', data=body, headers={'Authorization': 'Bearer ' + KEY, 'Content-Type': 'application/json'})
        try:
            with urllib.request.urlopen(req, timeout=120) as r: return json.load(r)
        except urllib.error.HTTPError as e:
            if e.code in (429, 529): time.sleep(2 ** attempt); continue
            return {'error': e.code, 'body': e.read().decode()[:500]}
        except Exception as e: time.sleep(2 ** attempt); last = str(e)
    return {'error': 'retries', 'body': last}

def main():
    A = os.path.join(os.path.dirname(OUT), '..')
    files = [l.strip() for g in sorted(os.listdir(A)) if g.startswith('group-') and g.endswith('.txt') for l in open(os.path.join(A, g)) if l.strip()]
    done = {json.loads(l)['path'] for l in open(OUT) if l.strip()} if os.path.exists(OUT) else set()
    todo = [f for f in files if f not in done]; print(f'{len(files)} files, {len(done)} done, {len(todo)} to do', flush=True)
    out = open(OUT, 'a')
    with cf.ThreadPoolExecutor(4) as ex:
        for f, facts, r in ex.map(lambda f: (f, state_of(f)['facts'], ask(state_of(f))), todo):
            out.write(json.dumps({'path': f, 'facts': facts, 'response': r}) + '\n'); out.flush()
            print(f, 'ok' if 'answers' in r else r.get('error'), flush=True)
    print('done', flush=True)

if __name__ == '__main__': main()
