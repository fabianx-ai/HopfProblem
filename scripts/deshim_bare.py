#!/usr/bin/env python3
"""Replace bare mo1973-suffixed references with their renamed stems."""
import json, re, glob
renames = json.load(open('/home/glm/s6-notes/hopf-lib-a/sw-renames.json'))
# oldlast = the ORIGINAL suffixed last segment (as it appears bare in files)
pairs = sorted(((old.split('.')[-1], new.split('.')[-1]) for old, new in renames.items()),
               key=lambda kv: -len(kv[0]))
total = 0
for f in sorted(glob.glob('Lib/**/*.lean', recursive=True)) + sorted(glob.glob('Hopf/**/*.lean', recursive=True)):
    s = open(f).read()
    orig = s
    for oldlast, newlast in pairs:
        s = re.sub(r'(?<!\w)' + re.escape(oldlast) + r'\b', newlast, s)
    if s != orig:
        open(f, 'w').write(s)
        total += 1
        print('rewritten:', f)
print('files rewritten:', total)
