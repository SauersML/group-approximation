#!/usr/bin/env python3
"""Primary cheap-test census of reduced LOTs on n vertices for one shape (no linear programs).
usage: census8p.py n shape_index outdir
Enumeration as census.py.  Each reduced LOT is tested by injectivity, the one-cycle criterion
and the I-test; the others are deduped by canonical form and written as survivors for the
second pass (lot2 / lot3 / lot4 / weight test)."""
import sys, json, itertools, time, os
from census import free_trees, automorphisms, canon_lot
from lot import test_inj, test_IT, test_itest, diameter

def main():
    n, si, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    tree = free_trees(n)[si]; m = n - 1; t0 = time.time()
    auts = automorphisms(n, tree)
    deg = [0] * n
    for u, v in tree: deg[u] += 1; deg[v] += 1
    leaves = [v for v in range(n) if deg[v] == 1]
    tally = {'n': n, 'shape': si, 'tree': tree, 'diam': diameter(n, [(u, 0, v) for u, v in tree]),
             'auts': len(auts), 'labellings': 0, 'reduced': 0, 'first_test_over_reduced': {}}
    surv = set(); d = tally['first_test_over_reduced']
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
            if test_inj(n, E): name = 'inj'
            elif test_IT(n, E): name = 'IT'
            elif test_itest(n, E): name = 'itest'
            else: name = 'survivor'; surv.add(canon_lot(E, auts))
            d[name] = d.get(name, 0) + 1
    tally['survivor_classes'] = len(surv); tally['seconds'] = round(time.time() - t0, 1)
    base = os.path.join(out, 'n%d_s%d' % (n, si))
    with open(base + '_tally.json', 'w') as fh: json.dump(tally, fh)
    with open(base + '_survivors.jsonl', 'w') as fh:
        for s in sorted(surv): fh.write(json.dumps(s) + '\n')
    print(json.dumps(tally), flush=True)

if __name__ == '__main__':
    main()
