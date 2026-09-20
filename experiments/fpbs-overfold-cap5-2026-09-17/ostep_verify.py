"""Independent check (no shared code with lcheck.c / deep5.c) of the (O-step)
violations that lcheck reports on the forced j=2, law-8 witness.

For a seed set P, ell(P) = least number of lawful seeds whose fold-closure
contains cl(P) & ker m.  (O-step) asks for some s in P with
ell(P) <= ell(P - s) + 1.  For P = {s, t} with s, t overfold this fails iff
ell({s}) = ell({t}) = 0 and ell({s, t}) >= 2.  This script checks exactly that,
testing EVERY lawful pair (u, v) with m(u) = m(v) (not only representatives)
for ell = 1, and a two-lawful-seed witness for ell <= 2.

Usage: python3 ostep_verify.py inst.txt u1 v1 u2 v2
"""
import itertools
import sys


def load(path):
    tok = open(path).read().split()
    p = 0
    V, n = int(tok[0]), int(tok[1]); p = 2
    nb = []
    for _ in range(V):
        nb.append([int(x) for x in tok[p:p + 4]]); p += 4
    m = [int(x) for x in tok[p:p + V]]; p += V
    return V, nb, m


def closure(V, nb, pairs):
    """Finest partition that merges `pairs` and is closed under folding:
    u ~ v and both have a k-edge  =>  their k-neighbours are merged.  Edges of
    one vertex with the same label also fold (the base)."""
    par = list(range(V))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    changed = True
    work = list(pairs)
    while True:
        for u, v in work:
            a, b = find(u), find(v)
            if a != b:
                par[a] = b
        work = []
        # fold: in each block, all k-neighbours must coincide
        seen = {}
        for v in range(V):
            r = find(v)
            for k in range(4):
                w = nb[v][k]
                if w < 0:
                    continue
                key = (r, k)
                if key in seen:
                    if find(seen[key]) != find(w):
                        work.append((seen[key], w))
                else:
                    seen[key] = w
        if not work:
            break
    return [find(v) for v in range(V)]


def kerpairs(V, m, lab):
    """Generating pairs of lab & ker m (v with the first vertex of its
    (fibre, block) class)."""
    first = {}
    out = []
    for v in range(V):
        key = (m[v], lab[v])
        if key in first:
            out.append((first[key], v))
        else:
            first[key] = v
    return out


def contains(lab, pairs):
    return all(lab[u] == lab[v] for u, v in pairs)


def main():
    V, nb, m = load(sys.argv[1])
    s = (int(sys.argv[2]), int(sys.argv[3]))
    t = (int(sys.argv[4]), int(sys.argv[5]))
    print('seeds', s, 'overfold' if m[s[0]] != m[s[1]] else 'lawful',
          t, 'overfold' if m[t[0]] != m[t[1]] else 'lawful')
    base = closure(V, nb, [])
    zero = {}
    for name, P in (('{s}', [s]), ('{t}', [t]), ('{s,t}', [s, t])):
        tgt = kerpairs(V, m, closure(V, nb, P))
        zero[name] = contains(base, tgt)
        print(name, 'ell = 0:', zero[name], flush=True)
    tgt = kerpairs(V, m, closure(V, nb, [s, t]))
    lawful = [(u, v) for u, v in itertools.combinations(range(V), 2)
              if m[u] == m[v] and base[u] != base[v]]
    print('lawful pairs not merged in base:', len(lawful), flush=True)
    one = [q for q in lawful if contains(closure(V, nb, [q]), tgt)]
    print('{s,t} single lawful seeds that suffice:', len(one), flush=True)
    # ell <= 2: search pairs among distinct single-seed closures
    cls = {}
    for q in lawful:
        first = {}
        key = tuple(first.setdefault(c, len(first)) for c in closure(V, nb, [q]))
        cls.setdefault(key, q)
    reps = list(cls.values())
    print('distinct single lawful closures:', len(reps), flush=True)
    two = None
    for a, b in itertools.combinations(reps, 2):
        if contains(closure(V, nb, [a, b]), tgt):
            two = (a, b)
            break
    print('{s,t} two-seed lawful witness:', two)
    ok = zero['{s}'] and zero['{t}'] and (not one) and two is not None
    print('VERDICT: ell({s})=ell({t})=0 needed; ell({s,t}) =',
          2 if ok else '?', '->', 'O-STEP FAILS' if ok else 'no violation shown')


if __name__ == '__main__':
    main()
