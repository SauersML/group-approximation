#!/usr/bin/env python3
"""Exhaustive census of reduced LOTs on n vertices for one tree shape.

usage: census.py n shape_index outdir     (shape_index -1 lists the shapes)
Covers every LOT whose underlying tree is the shape: all orientations with edge 0 fixed
(reversing every edge gives a homeomorphic complex via x -> x^-1), all labellings.
Classes are identified up to shape automorphisms and global reversal.
"""
import sys, json, itertools, time, os
from lot import certify, diameter

def canon_tree(n, pairs):
    adj = [[] for _ in range(n)]
    for u, v in pairs: adj[u].append(v); adj[v].append(u)
    deg = [len(x) for x in adj]; removed = [False] * n; rem = n
    leaves = [v for v in range(n) if deg[v] <= 1]
    while rem > 2:
        new = []
        for v in leaves:
            removed[v] = True; rem -= 1
            for w in adj[v]:
                if not removed[w]:
                    deg[w] -= 1
                    if deg[w] == 1: new.append(w)
        leaves = new
    def enc(v, p):
        return '(' + ''.join(sorted(enc(w, v) for w in adj[v] if w != p)) + ')'
    return min(enc(c, -1) for c in range(n) if not removed[c])

def free_trees(n):
    trees = {'()': []}
    for k in range(2, n + 1):
        nxt = {}
        for pairs in trees.values():
            for v in range(k - 1):
                P = pairs + [(v, k - 1)]
                nxt.setdefault(canon_tree(k, P), P)
        trees = nxt
    return [trees[key] for key in sorted(trees)]

def automorphisms(n, pairs):
    es = {frozenset(p) for p in pairs}
    return [p for p in itertools.permutations(range(n))
            if all(frozenset((p[u], p[v])) in es for u, v in pairs)]

def canon_lot(E, auts):
    best = None
    for p in auts:
        for rev in (False, True):
            F = tuple(sorted((p[t], p[l], p[i]) if rev else (p[i], p[l], p[t]) for (i, l, t) in E))
            if best is None or F < best: best = F
    return best

def main():
    n, si, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    shapes = free_trees(n)
    if si < 0:
        for k, s in enumerate(shapes): print(k, s, 'diam', diameter(n, [(u, 0, v) for u, v in s]))
        return
    tree = shapes[si]; m = n - 1; t0 = time.time()
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
            if any(v not in ls for v in leaves): continue          # boundary reduced
            key = set(); bad = False
            for (i, t), l in zip(ends, labs):                        # interior reduced
                a, b = (i, 's', l), (t, 't', l)
                if a in key or b in key: bad = True; break
                key.add(a); key.add(b)
            if bad: continue
            E = [(i, l, t) for (i, t), l in zip(ends, labs)]
            tally['reduced'] += 1
            cf = canon_lot(E, auts)
            if cf in seen: continue
            seen.add(cf); tally['classes'] += 1
            red, name, cert = certify(n, list(cf))
            if red[0] != n: name = 'NOT_REDUCED'                    # must never happen
            tally['first_test'][str(name)] = tally['first_test'].get(str(name), 0) + 1
            if name in ('itest', 'weight'): certs.append({'lot': cf, 'test': name, 'cert': cert})
            if name is None or name == 'NOT_REDUCED': surv.append(cf)
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
