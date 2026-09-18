#!/usr/bin/env python3
"""Checks for fpbs-quasiconvex-null-small-classes-exist-on-free-boundary.

Letters of F_2 = <a,b>: 'a','A' (= a^-1), 'b','B'.

Part 1 (Lemma 1 of the proof).  Enumerate every connected folded labelled graph with at most 4 vertices
(a, b are partial injections of the vertex set) that is NOT a covering of the rose.  For each, compute the
spectral radius rho of the alternating-walk transfer matrix M on states (v, next type) and check rho < 2.
Also find, for the disjoint union of all graphs with <= 3 vertices, a shortest alternating word that is
readable from no vertex of any of them (an alternating killing word).

Part 2 (Theorem, item (b), finite-stage sanity check).  Build the symmetric odometer code F on Z/q with
q = 2^k: parity types (even -> a-type, odd -> b-type), F(-y) = F(y)^-1 off the two self-symmetric residues,
and one inserted killing word.  Check reducedness of every window, the inversion identity
prefix_m(x)^-1 = prefix_m(-x-m-1), and print the Haar shadow term
T_m = sum_{|w|=m} f(w) f(w^-1)  (f = window frequency), whose sum over m must grow like log.
"""
import itertools, random
import numpy as np

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def partial_injections(n):
    out = []
    for k in range(n + 1):
        for dom in itertools.combinations(range(n), k):
            for img in itertools.permutations(range(n), k):
                out.append(dict(zip(dom, img)))
    return out


def connected(n, pa, pb):
    adj = {v: set() for v in range(n)}
    for p in (pa, pb):
        for u, v in p.items():
            adj[u].add(v); adj[v].add(u)
    seen, st = {0}, [0]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v); st.append(v)
    return len(seen) == n


def step(graph, v, letter):
    pa, pb = graph
    p = pa if letter in 'aA' else pb
    if letter in 'ab':
        return p.get(v)
    for u, w in p.items():
        if w == v:
            return u
    return None


def rho_alternating(n, pa, pb):
    # states: (v, 0) = next letter a-type, (v, 1) = next letter b-type
    M = np.zeros((2 * n, 2 * n))
    for v in range(n):
        for t, letters in ((0, 'aA'), (1, 'bB')):
            for L in letters:
                w = step((pa, pb), v, L)
                if w is not None:
                    M[2 * v + t, 2 * w + (1 - t)] += 1
    return max(abs(np.linalg.eigvals(M)))


def readable_somewhere(graphs, word):
    for g, n in graphs:
        for v in range(n):
            u = v
            for L in word:
                u = step(g, u, L)
                if u is None:
                    break
            else:
                return True
    return False


def part1():
    worst = 0.0
    count = 0
    small = []
    for n in range(1, 5):
        pis = partial_injections(n)
        for pa in pis:
            for pb in pis:
                if not connected(n, pa, pb):
                    continue
                covering = len(pa) == n and len(pb) == n
                if covering:
                    continue
                r = rho_alternating(n, pa, pb)
                worst = max(worst, r)
                count += 1
                if n <= 3:
                    small.append(((pa, pb), n))
    print(f"Part 1: {count} connected non-covering folded graphs with <= 4 vertices; max rho = {worst:.6f} (< 2)")
    # shortest alternating killing word for the union of those with <= 3 vertices, starting with a-type
    for m in range(1, 40):
        for signs in itertools.product((0, 1), repeat=m):
            w = ''.join(('aA' if i % 2 == 0 else 'bB')[s] for i, s in enumerate(signs))
            if not readable_somewhere(small, w):
                print(f"  shortest alternating killing word for all {len(small)} graphs with <= 3 vertices:"
                      f" length {m}: {w}")
                return w
    return None


def inv(w):
    return ''.join(INV[c] for c in reversed(w))


def part2(kill, k=15, seed=1):
    """Hierarchical (Toeplitz part + one overwrite) symmetric code, as in Step 2 of the proof."""
    random.seed(seed)
    q = 4
    F = {1: random.choice('bB')}
    F[3] = INV[F[1]]
    stage = 0
    while q < 2 ** k:
        q2 = 2 * q
        G = {}
        for y in range(q2):
            if y % q in F:
                G[y] = F[y % q]
        L = random.choice('aA' if (q2 // 4) % 2 == 0 else 'bB')
        G[q2 // 4] = L
        G[3 * q2 // 4] = INV[L]
        q, F = q2, G
        stage += 1
        if stage == 6:   # overwrite stage: insert the killing word and its mirror
            r = q // 8 + 2
            r += (r % 2)  # the killing word starts with an a-type letter, so r must be even
            for i, c in enumerate(kill):
                F[r + i] = c
                F[(q - r - i) % q] = INV[c]
    Fl = [F.get(y) for y in range(q)]
    bad = sum(1 for y in range(q) if Fl[y] and Fl[(y + 1) % q] and Fl[(y + 1) % q] == INV[Fl[y]])
    sym = sum(1 for y in range(1, q) if y != q // 2 and Fl[(q - y) % q] != INV[Fl[y]])
    print(f"Part 2: q = {q}; holes = {[y for y in range(q) if Fl[y] is None]}; non-reduced pairs = {bad};"
          f" symmetry failures = {sym}")
    ok = tot = 0
    for _ in range(3000):
        x = random.randrange(q); m = random.randrange(1, 300)
        w1 = [Fl[(x + i) % q] for i in range(1, m + 1)]
        w2 = [Fl[(-x - m - 1 + i) % q] for i in range(1, m + 1)]
        if None in w1 or None in w2:
            continue
        tot += 1; ok += inv(''.join(w1)) == ''.join(w2)
    print(f"  inversion identity prefix_m(x)^-1 = prefix_m(-x-m-1): {ok}/{tot} (hole windows skipped)")
    kw = ''.join(Fl[r:r + len(kill)])
    print(f"  killing word present at residue {r}: {kw == kill}")
    cum = 0.0
    prev = 0
    for m in range(1, 1025):
        if m & (m - 1) and m != 1024:
            continue
        freq = {}
        for x in range(q):
            w = [Fl[(x + i) % q] for i in range(1, m + 1)]
            if None in w:
                continue
            w = ''.join(w)
            freq[w] = freq.get(w, 0) + 1.0 / q
        T = sum(f * freq.get(inv(w), 0.0) for w, f in freq.items())
        print(f"  m = {m:5d}: cells = {len(freq):6d} (cells/m = {len(freq)/m:6.2f}), T_m = {T:.3e}, m*T_m = {m*T:.3f}")


if __name__ == '__main__':
    w = part1()
    part2(w)
