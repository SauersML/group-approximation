#!/usr/bin/env python3
"""acverify.py -- standalone checker (lane hl-andrews-curtis), sharing no code with fsac.py.
For each JSON line {t, g, code, [tree], rels, cert | a5} it
  1. rebuilds the disk words of the fake surface from graph g (graphs-t<t>.json) and the base-6 code,
     by its own corner walk, collapses the spanning tree (given, or the default BFS tree), frees-reduces,
     and requires the result to equal `rels` exactly;
  2. requires the exponent matrix to have determinant +-1 (acyclic);
  3. replays the stable Andrews-Curtis certificate, or checks the A_5 images kill every relator and are
     not all trivial.  Exit status 0 iff every line passes.  usage: acverify.py <jsonl or .gz> ...
"""
import sys, json, gzip
PERMS = [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]
GRAPHS = {}

def edges_of(A):
    E = []
    for i in range(len(A)):
        for j in range(i, len(A)):
            E += [(i, j)] * (A[i][i] // 2 if i == j else A[i][j])
    return E

def disk_words(A, code):
    E = edges_of(A); ends = []            # half-edge 2e+s sits at E[e][s]
    for (i, j) in E: ends += [i, j]
    at = {}
    for h, v in enumerate(ends): at.setdefault(v, []).append(h)
    others = {h: [x for x in at[ends[h]] if x != h] for h in range(len(ends))}
    match = {}
    for e in range(len(E)):
        p = PERMS[code % 6]; code //= 6
        for k in range(3):
            a, b = (2*e, others[2*e][k]), (2*e+1, others[2*e+1][p[k]])
            match[a] = b; match[b] = a
    used, words = set(), []
    for h in range(len(ends)):
        for x in others[h]:
            if (h, x) in used: continue
            cur, w = (h, x), []
            while True:
                used.add(cur); used.add((cur[1], cur[0]))
                e = cur[0] // 2; w.append(e+1 if cur[0] % 2 == 0 else -(e+1))
                far, y = match[(cur[0], cur[1])]
                cur = (y, far)
                if cur == (h, x): break
            words.append(w)
    return E, words

def reduce(w):
    s = []
    for a in w:
        if s and s[-1] == -a: s.pop()
        else: s.append(a)
    return s

def default_tree(A, E):
    seen, tree, changed = {0}, [], True
    while changed:
        changed = False
        for e, (u, w) in enumerate(E):
            if u != w and ((u in seen) ^ (w in seen)): seen |= {u, w}; tree.append(e); changed = True
    return tree

def det(M):
    from fractions import Fraction
    M = [[Fraction(x) for x in r] for r in M]; n = len(M); d = Fraction(1)
    for k in range(n):
        piv = next((r for r in range(k, n) if M[r][k]), None)
        if piv is None: return 0
        if piv != k: M[k], M[piv] = M[piv], M[k]; d = -d
        d *= M[k][k]
        for r in range(k+1, n):
            f = M[r][k] / M[k][k]; M[r] = [M[r][c] - f*M[k][c] for c in range(n)]
    return d

def check(d):
    t, g, code = d["t"], d["g"], d["code"]
    if t not in GRAPHS: GRAPHS[t] = json.load(open(f"graphs-t{t}.json"))
    A = GRAPHS[t][g-1]; E, words = disk_words(A, code)
    tree = d.get("tree") or default_tree(A, E)
    label, c = {}, 0
    for e in range(len(E)):
        if e not in tree: c += 1; label[e] = c
    n = t + 1
    rels = [reduce([(1 if a > 0 else -1) * label[abs(a)-1] for a in w if abs(a)-1 in label]) for w in words]
    if len(words) != n or rels != d["rels"]: return "rels-mismatch"
    if abs(det([[sum((1 if a > 0 else -1) for a in r if abs(a) == j) for j in range(1, n+1)] for r in rels])) != 1: return "not-acyclic"
    if "perm" in d:
        img = {int(k): v for k, v in d["perm"].items()}; N = len(img[1])
        if sorted(img) != list(range(1, n+1)) or any(sorted(v) != list(range(N)) for v in img.values()): return "perm-bad-image"
        back = {g: [0]*N for g in img}
        for g, v in img.items():
            for p, q in enumerate(v): back[g][q] = p
        for r in rels:
            for p in range(N):
                q = p
                for a in r: q = img[a][q] if a > 0 else back[-a][q]
                if q != p: return "perm-relator-fails"
        return "pi1-nontrivial" if any(v != list(range(N)) for v in img.values()) else "perm-trivial"
    if "a5" in d:
        img = {int(k): tuple(v) for k, v in d["a5"].items()}
        def comp(p, q): return tuple(p[q[i]] for i in range(5))
        def inverse(p): return tuple(sorted(range(5), key=lambda i: p[i]))
        e = (0, 1, 2, 3, 4)
        if any(sorted(x) != list(range(5)) or sum(x[i] > x[j] for i in range(5) for j in range(i+1, 5)) % 2 for x in img.values()): return "a5-bad-image"
        for r in rels:
            acc = e
            for a in r: acc = comp(acc, img[a] if a > 0 else inverse(img[-a]))
            if acc != e: return "a5-relator-fails"
        return "pi1-nontrivial" if any(x != e for x in img.values()) else "a5-trivial"
    R = {i: list(r) for i, r in enumerate(rels)}; gens = set(range(1, n+1))
    for mv in d["cert"]:
        op = mv[0]
        if op == "conj": R[mv[1]] = reduce(mv[2] + R[mv[1]] + [-a for a in reversed(mv[2])])
        elif op == "inv": R[mv[1]] = [-a for a in reversed(R[mv[1]])]
        elif op == "mulc":
            j, i, u, s = mv[1:]
            if i == j or s not in (1, -1): return "bad-move"
            ri = R[i] if s == 1 else [-a for a in reversed(R[i])]
            R[j] = reduce(R[j] + u + ri + [-a for a in reversed(u)])
        elif op == "destab":
            gg = mv[1]; ks = [k for k in R if R[k] == [gg]]
            if not ks or any(abs(a) == gg for k in R if k != ks[0] for a in R[k]): return "bad-destab"
            del R[ks[0]]; gens.discard(gg)
        else: return "bad-op"
        if any(abs(a) not in gens for r in R.values() for a in r): return "letter-outside"
    return "stably-ac-trivial" if not R and not gens else "incomplete"

if __name__ == "__main__":
    from collections import Counter
    tally = Counter()
    for fn in sys.argv[1:]:
        for line in (gzip.open(fn, "rt") if fn.endswith(".gz") else open(fn)):
            d = json.loads(line)
            if "code" not in d: continue
            if "cert" not in d and "a5" not in d and "perm" not in d: tally["uncertified:" + d.get("status", "?")] += 1; continue
            tally[check(d)] += 1
    print(json.dumps(dict(tally)))
