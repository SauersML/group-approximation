import json, glob, collections
tot = collections.Counter()
for f in sorted(glob.glob('out_*.jsonl')):
    rs = [json.loads(l) for l in open(f)]
    c = collections.Counter()
    for r in rs:
        fin = r['finH'] is not None and r['finV'] is not None
        half = (r['finH'] is None) != (r['finV'] is None)
        keys = [k for k in r if k.startswith('R')]
        last = r[keys[-1]]
        if fin:
            c['reducible(certified finite), R4 ' + ('SAT' if r['R4sNone'][0] else 'UNSAT')] += 1
        else:
            tag = 'not-certified-finite' + (' (one side finite!)' if half else '')
            c[f"{tag}: {'UNSAT at '+keys[-1] if not last[0] else 'SAT through '+keys[-1]}"] += 1
    print(f, len(rs), dict(c))
    tot.update(c)
print('TOTAL', sum(tot.values()), dict(tot))
