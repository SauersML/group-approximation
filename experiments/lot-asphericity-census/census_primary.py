#!/usr/bin/env python3
"""Exhaustive primary-source census of reduced LOTs on n vertices for one tree shape.
usage: census_primary.py n shape_index outdir
Same enumeration as census.py (all orientations with edge 0 fixed, all labellings, classes up
to shape automorphisms and global reversal), certified with lot_primary.certify_primary."""
import sys, json, itertools, time, os
from census import free_trees, automorphisms, canon_lot
from lot import diameter
from lot_primary import certify_primary

def main():
    n, si, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    tree = free_trees(n)[si]; m = n - 1; t0 = time.time()
    auts = automorphisms(n, tree)
    deg = [0] * n
    for u, v in tree: deg[u] += 1; deg[v] += 1
    leaves = [v for v in range(n) if deg[v] == 1]
    tally = {'n': n, 'shape': si, 'tree': tree, 'diam': diameter(n, [(u, 0, v) for u, v in tree]),
             'auts': len(auts), 'labellings': 0, 'reduced': 0, 'classes': 0, 'first_test': {}}
    seen, certs, surv = set(), [], []
    for orient in itertools.product((0, 1), repeat=m - 1):
        ends = [tree[0]] + [(u, v) if o == 0 else (v, u) for (u, v), o in zip(tree[1:], orient)]
        choices = [[z for z in range(n) if z not in e] for e in ends]
        for labs in itertools.product(*choices):
            tally['labellings'] += 1
            ls = set(labs)
            if any(v not in ls for v in leaves): continue
            key, bad = set(), False
            for (i, t), l in zip(ends, labs):
                a, b = (i, 's', l), (t, 't', l)
                if a in key or b in key: bad = True; break
                key.add(a); key.add(b)
            if bad: continue
            E = [(i, l, t) for (i, t), l in zip(ends, labs)]
            tally['reduced'] += 1
            cf = canon_lot(E, auts)
            if cf in seen: continue
            seen.add(cf); tally['classes'] += 1
            name, cert = certify_primary(n, list(cf))
            tally['first_test'][str(name)] = tally['first_test'].get(str(name), 0) + 1
            if name not in ('inj', 'IT', None): certs.append({'lot': cf, 'test': name, 'cert': cert})
            if name is None: surv.append(cf)
    tally['survivors'] = len(surv); tally['seconds'] = round(time.time() - t0, 1)
    base = os.path.join(out, 'n%d_s%d' % (n, si))
    with open(base + '_tally.json', 'w') as fh: json.dump(tally, fh)
    with open(base + '_certs.jsonl', 'w') as fh:
        for c in certs: fh.write(json.dumps(c) + '\n')
    with open(base + '_survivors.jsonl', 'w') as fh:
        for s in surv: fh.write(json.dumps(s) + '\n')
    print(json.dumps(tally), flush=True)

if __name__ == '__main__':
    main()
