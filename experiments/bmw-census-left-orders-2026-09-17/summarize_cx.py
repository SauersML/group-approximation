# Tabulate the four-vertex censuses (out_cx4_33.jsonl for degree (3,3), out_cx_34.jsonl for degree (3,4)) and assert
# that every class is certified reducible or stops UNSAT.
import json, collections
for deg, name, ncls in (('(3,3)', 'out_cx4_33.jsonl', 11), ('(3,4)', 'out_cx_34.jsonl', 98)):
    recs = [json.loads(l) for l in open(name)]; assert sorted(r['idx'] for r in recs) == list(range(ncls))
    t = collections.Counter(); hard = []; red_unsat = []; maxord = 0
    for r in recs:
        stages = [k for k in r if k.startswith('R')]
        if r['finH'] is not None and r['finV'] is not None:
            t['reducible'] += 1; maxord = max(maxord, r['finH'], r['finV'])
            if not r['R4sNone'][0]: red_unsat.append((r['idx'], r['finH'], r['finV']))
        else:
            assert r[stages[-1]][0] is False, r
            t['candidates'] += 1; t['UNSAT at ' + stages[-1]] += 1
            if stages[-1] == 'R8s2': hard.append(r['idx'])
    print(deg, dict(t), 'max image order', maxord, 'reducible but R4 UNSAT', red_unsat, 'needed R8s2', hard)
