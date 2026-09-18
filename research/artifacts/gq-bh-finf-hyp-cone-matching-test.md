# Cone-matching test on right-angled Coxeter groups (bh-finf-hyp, 2026-09-18)

- **The run.** One Slurm job, 1328148 (partition msismall, node acl43, 4 cores, 19 s wall,
  367 MB). Output is in `/projects/standard/hsiehph/sauer354/bh-finf-hyp/` (`cmp-1328148.out`,
  `cmp_results.jsonl`).
- **What it tests.**
  - Horofunction atoms of `B_n` are classes of `x` under `d_x|_{B_n}` modulo constants. Word
    lengths are exact, by Tits' deletion rule for right-angled Coxeter groups. Elements are keyed by
    their projections onto pairs of non-commuting generators (the projection lemma for traces).
  - For each generator `k`, and each atom `D` of `B_n` detected on the sphere of radius `R0`, we
    look for a **witness** that `kD` is not an atom. A witness is a point `w` of the smallest window
    class containing `kD ∩ window` whose preimage `k^{-1}w` lies outside `D`. A witness is an exact
    certificate. The absence of one is only evidence.
  - `badchild` counts bad atoms that have a bad child atom. `chain` is the longest nested chain of
    bad atoms starting at that level.

## Results (every generator gives the same numbers)

| group | R0, N | level n: atoms / bad / bad with bad child |
|---|---|---|
| free3 = Z/2*Z/2*Z/2 (tree; calibration) | 12, 6 | 1: 3/1/0; 2: 6/0/0; 3: 12/0/0; 4: 24/0/0; 5: 48/0/0 |
| square = D_∞ × D_∞ (Z² grid; positive control) | 24, 10 | n = 1..9: 8n / 4 / 4 (chain 9 from level 1) |
| pentagon (right-angled pentagon group, hyperbolic, ∂ = S¹) | 9, 5 | 1: 10/5/4; 2: 30/4/4; 3: 80/4/4; 4: 210/4/– |
| pentagon | 8, 6 | 1: 10/5/4; 2: 30/4/4; 3: 80/4/4; 4: 210/4/4; 5: 550/4/– (chain 5 from level 1) |

**Reading.**
- **Calibration passes.** In the tree, only the atom at the root direction fails, at level 1, as
  predicted.
- **The positive control behaves as predicted.** The grid fails at its 4 corners at every level.
- **Pentagon.** For every generator, exactly 4 atoms per level fail, and they form nested chains
  through every computed level. This is the corner signature.
- **Mechanism (proposed).** The reflection `s_i` fixes the two endpoints of its wall.
  - A front window at such an endpoint straddles the wall.
  - There `d(s_i, ·) − d(1, ·)` takes both values `+1` and `−1`.
  - So Theorem 1 of `hyperbolic-cone-matching-holds-off-the-branch-locus` cannot apply there.
    These endpoints are branch points.
  - This mechanism is not proved; the data are exact at each tested level.

## The script (`cmp_test.py`)

```python
#!/usr/bin/env python3
"""Cone-matching test for right-angled Coxeter groups (graph products of Z/2).

Atoms of the n-ball B_n: classes of x under d_x|B_n modulo constants (horofunction atoms, BBM/BBMZ).
For a generator k and an infinite atom D (detected on the sphere of radius R0), kD is an atom
iff kD equals the smallest atom containing it. We look for an exact witness of failure: a point w
in the window class C (smallest level-m class containing the window images kX_D) with k^{-1}w
outside D. A witness proves that kD is not an atom. We then measure persistence: chains
D_1 > D_2 > ... of nested non-matching atoms. Persistent chains at every level are the cone-matching
failures that condition (C) excludes.

Controls: free3 = Z/2*Z/2*Z/2 (Cayley graph a tree: no failures expected for n >= 1);
square = D_inf x D_inf (Cayley graph the Z^2 grid: failures at corners expected at every level).
Test: pentagon (right-angled pentagon group, hyperbolic with circle boundary).
"""
import sys, time, json
from multiprocessing import Pool

G = {}


def setup(nv, edges):
    comm = [[False] * nv for _ in range(nv)]
    for a, b in edges:
        comm[a][b] = comm[b][a] = True
    pairs = [(u, v) for u in range(nv) for v in range(u + 1, nv) if not comm[u][v]]
    pair_of = [[i for i, (u, v) in enumerate(pairs) if x in (u, v)] for x in range(nv)]
    return comm, pairs, pair_of


def rappend(w, v, comm):
    i = len(w) - 1
    while i >= 0:
        u = w[i]
        if u == v:
            del w[i]
            return i
        if not comm[u][v]:
            break
        i -= 1
    w.append(v)
    return -1


def lmul(v, w, comm):
    n = len(w)
    j = 0
    while j < n:
        u = w[j]
        if u == v:
            return w[:j] + w[j + 1:]
        if not comm[u][v]:
            break
        j += 1
    return [v] + w


def ekey(w, npairs, pair_of):
    proj = [[] for _ in range(npairs)]
    for v in w:
        for p in pair_of[v]:
            proj[p].append(v)
    return tuple(tuple(x) for x in proj)


def ball(R, nv, comm, npairs, pair_of):
    words = [[]]
    keys = {ekey([], npairs, pair_of): 0}
    level = [0]
    parent = [-1]
    letter = [-1]
    frontier = [0]
    for r in range(1, R + 1):
        new = []
        for idx in frontier:
            w = words[idx]
            for s in range(nv):
                w2 = list(w)
                if rappend(w2, s, comm) != -1:
                    continue
                k = ekey(w2, npairs, pair_of)
                if k in keys:
                    continue
                keys[k] = len(words)
                words.append(w2)
                level.append(r)
                parent.append(idx)
                letter.append(s)
                new.append(len(words) - 1)
        frontier = new
    return words, keys, level, parent, letter


def winit(comm, ops, letter, sizeN, N):
    G['comm'] = comm
    G['ops'] = ops
    G['letter'] = letter
    G['sizeN'] = sizeN
    G['N'] = N


def wkeys(chunk):
    comm = G['comm']; ops = G['ops']; letter = G['letter']; sizeN = G['sizeN']; N = G['N']
    out = []
    for wx in chunk:
        state = list(reversed(wx))
        dist = [0] * sizeN
        dist[0] = len(state)
        ust = []
        for op in ops:
            if op >= 0:
                v = letter[op]
                i = len(state) - 1
                tok = -1
                while i >= 0:
                    u = state[i]
                    if u == v:
                        del state[i]
                        tok = i
                        break
                    if not comm[u][v]:
                        break
                    i -= 1
                if tok == -1:
                    state.append(v)
                ust.append((v, tok))
                dist[op] = len(state)
            else:
                v, tok = ust.pop()
                if tok == -1:
                    state.pop()
                else:
                    state.insert(tok, v)
        base = dist[0]
        out.append(bytes([d - base + N for d in dist]))
    return out


def analyse(name, nv, edges, R0, N, ncpu, log):
    t0 = time.time()
    comm, pairs, pair_of = setup(nv, edges)
    npairs = len(pairs)
    R = R0 + 2
    words, keys, level, parent, letter = ball(R, nv, comm, npairs, pair_of)
    cnt = [0] * (R + 1)
    for l in level:
        cnt[l] += 1
    size = [sum(cnt[:n + 1]) for n in range(N + 1)]
    sizeN = size[N]
    log(f"[{name}] R0={R0} N={N} sphere sizes {cnt} |B_N|={sizeN} ball={len(words)} t={time.time()-t0:.1f}s")
    children = [[] for _ in range(sizeN)]
    for i in range(1, sizeN):
        children[parent[i]].append(i)
    ops = []
    stack = [(0, iter(children[0]))]
    while stack:
        node, it = stack[-1]
        c = next(it, None)
        if c is None:
            stack.pop()
            if node != 0:
                ops.append(-1)
        else:
            ops.append(c)
            stack.append((c, iter(children[c])))
    shell = [i for i in range(len(words)) if R0 - 2 <= level[i] <= R0 + 2]
    chunks = [[words[i] for i in shell[j:j + 1000]] for j in range(0, len(shell), 1000)]
    with Pool(ncpu, initializer=winit, initargs=(comm, ops, letter[:sizeN], sizeN, N)) as pool:
        res = pool.map(wkeys, chunks)
    fullkey = {}
    pos = 0
    for ch in res:
        for kb in ch:
            fullkey[shell[pos]] = kb
            pos += 1
    log(f"[{name}] keys for {len(shell)} shell points t={time.time()-t0:.1f}s")
    M = [i for i in shell if level[i] == R0]
    W1 = [i for i in shell if level[i] in (R0 - 1, R0 + 1)]
    byclass = [None] + [dict() for _ in range(N)]
    for m in range(1, N + 1):
        d = byclass[m]; sz = size[m]
        for i in W1:
            d.setdefault(fullkey[i][:sz], []).append(i)
    report = {'group': name, 'R0': R0, 'N': N, 'spheres': cnt, 'gens': {}}
    for k in range(nv):
        img = {}
        for i in M + W1:
            j = keys.get(ekey(lmul(k, words[i], comm), npairs, pair_of))
            assert j is not None and j in fullkey, (name, k, i)
            img[i] = j
        nonmatch = {}
        kids = {}
        per = []
        for n in range(1, N):
            szn = size[n]
            classes = {}
            for i in M:
                classes.setdefault(fullkey[i][:szn], []).append(i)
            nm = 0; cap = 0; nmroot = 0
            for D, X in classes.items():
                Y = [img[i] for i in X]
                mstar = 0
                for m in range(N, 0, -1):
                    sz = size[m]
                    c0 = fullkey[Y[0]][:sz]
                    if all(fullkey[y][:sz] == c0 for y in Y):
                        mstar = m
                        break
                bad = False
                if mstar == 0:
                    bad = True; nmroot += 1
                else:
                    if mstar == N:
                        cap += 1
                    C = fullkey[Y[0]][:size[mstar]]
                    for w in byclass[mstar].get(C, []):
                        if fullkey[img[w]][:szn] != D:
                            bad = True
                            break
                nonmatch[(n, D)] = bad
                if bad:
                    nm += 1
                if n + 1 < N:
                    kids[(n, D)] = {fullkey[i][:size[n + 1]] for i in X}
            per.append({'n': n, 'atoms': len(classes), 'nonmatch': nm, 'root_images': nmroot, 'cap': cap})
        chain = {}
        for n in range(N - 1, 0, -1):
            for (nn, D), bad in nonmatch.items():
                if nn != n:
                    continue
                if not bad:
                    chain[(n, D)] = 0
                    continue
                best = 0
                for c in kids.get((n, D), ()):
                    best = max(best, chain.get((n + 1, c), 0))
                chain[(n, D)] = 1 + best
        for row in per:
            n = row['n']
            row['nonmatch_with_nonmatch_child'] = sum(
                1 for (nn, D), bad in nonmatch.items()
                if nn == n and bad and n + 1 < N and any(nonmatch.get((n + 1, c), False) for c in kids.get((n, D), ())))
            row['max_chain_from_here'] = max([chain[(nn, D)] for (nn, D) in chain if nn == n] or [0])
        report['gens'][k] = per
        log(f"[{name}] k={k}: " + "; ".join(
            f"n={r['n']} atoms={r['atoms']} bad={r['nonmatch']} badchild={r['nonmatch_with_nonmatch_child']} "
            f"chain={r['max_chain_from_here']} cap={r['cap']}" for r in per))
    log(f"[{name}] done t={time.time()-t0:.1f}s")
    return report


def main():
    ncpu = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    T = time.time()
    out = open('cmp_results.jsonl', 'w')

    def log(s):
        print(s, flush=True)

    configs = [
        ('free3', 3, [], 12, 6),
        ('square', 4, [(0, 1), (1, 2), (2, 3), (3, 0)], 24, 10),
        ('pentagon', 5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 9, 5),
        ('pentagonB', 5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 8, 6),
    ]
    for name, nv, edges, R0, N in configs:
        if time.time() - T > 18 * 60:
            log(f"[{name}] skipped for time")
            continue
        rep = analyse(name, nv, edges, R0, N, ncpu, log)
        out.write(json.dumps(rep) + "\n")
        out.flush()
    log(f"ALL DONE t={time.time()-T:.1f}s")


if __name__ == '__main__':
    main()
```

## The job script

```bash
#!/bin/bash
#SBATCH -J bhfinf-cmp
#SBATCH -p ag2tb,msismall
#SBATCH -c 4
#SBATCH --mem=12G
#SBATCH --time=00:30:00
#SBATCH -o /projects/standard/hsiehph/sauer354/bh-finf-hyp/cmp-%j.out
#SBATCH -e /projects/standard/hsiehph/sauer354/bh-finf-hyp/cmp-%j.err
set -u
cd /projects/standard/hsiehph/sauer354/bh-finf-hyp || exit 1
PY=/usr/bin/python3.11
[ -x "$PY" ] || PY=$(command -v python3)
echo "host $(hostname) python $PY start $(date)"
"$PY" -u cmp_test.py 4
echo "end $(date) rc=$?"
```
