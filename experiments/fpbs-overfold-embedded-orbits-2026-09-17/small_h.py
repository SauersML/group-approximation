"""Search for Cayley levels with (E) at depth j and SMALL L_j-orbits.

For the Cayley level of G = <alpha, beta> <= Sym(d), the L_j-orbits are the
left cosets gH, H = <alpha, tau_j> (tau_j = t_j(alpha, beta)), all of size
|H|, and (E) at depth j holds iff the elements pi(u_c), c in V(C_j), lie in
pairwise distinct right cosets of H (u_c = BFS word o -> c in C_j).  Neither
test needs G itself, only H, so large G are cheap.

Question (E-B): is there s with, for every j, a level satisfying (E) at depth
j whose L_j-orbits all have size <= s?

Usage: python3 small_h.py j d trials seed hcap [mode]
  mode 'rand' : alpha, beta uniform in Sym(d)
  mode 'invol': alpha a random involution with few 2-cycles, beta uniform
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import Graph, gamma, A, t  # noqa: E402


def core_words(j):
    G = Graph(gamma([0], [0], [A, t(j)]), 1, [0], [0])
    return [G.word[v][1] for v in range(G.V)]


def mul(g, h):          # right action: x.(gh) = (x.g).h
    return tuple(h[g[i]] for i in range(len(g)))


def inv(g):
    r = [0] * len(g)
    for i, x in enumerate(g):
        r[x] = i
    return tuple(r)


def ev(word, al, be):
    ai, bi = inv(al), inv(be)
    g = tuple(range(len(al)))
    for (l, e) in word:
        s = (al if e == 1 else ai) if l == 'a' else (be if e == 1 else bi)
        g = mul(g, s)
    return g


def gen(gens, cap):
    e = tuple(range(len(gens[0])))
    els = {e}
    fr = [e]
    while fr:
        nf = []
        for g in fr:
            for s in gens:
                h = mul(g, s)
                if h not in els:
                    els.add(h)
                    nf.append(h)
                    if len(els) > cap:
                        return None
        fr = nf
    return els


def check(al, be, j, words, tj, hcap):
    tau = ev(tj, al, be)
    H = gen([al, tau], hcap)
    if H is None:
        return None
    us = [ev(w, al, be) for w in words]
    reps = []
    for u in us:
        ui = inv(u)
        for r in reps:
            if mul(r, ui) in H:
                return (len(H), False)
        reps.append(u)
    return (len(H), True)


def orbit_count(al, be):
    d = len(al)
    seen = {0}
    st = [0]
    while st:
        p = st.pop()
        for q in (al[p], be[p]):
            if q not in seen:
                seen.add(q)
                st.append(q)
    return len(seen) == d


def main():
    j, d, trials, seed, hcap = [int(x) for x in sys.argv[1:6]]
    mode = sys.argv[6] if len(sys.argv) > 6 else 'rand'
    rng = random.Random(seed)
    words = core_words(j)
    tj = t(j)
    best = None
    hist = {}
    for _ in range(trials):
        if mode == 'invol':
            al = list(range(d))
            k = rng.randint(1, max(1, d // 2))
            pts = rng.sample(range(d), 2 * k)
            for i in range(k):
                x, y = pts[2 * i], pts[2 * i + 1]
                al[x], al[y] = y, x
            al = tuple(al)
        else:
            al = list(range(d)); rng.shuffle(al); al = tuple(al)
        be = list(range(d)); rng.shuffle(be); be = tuple(be)
        if not orbit_count(al, be):
            continue
        r = check(al, be, j, words, tj, hcap)
        if r is None or not r[1]:
            continue
        hist[r[0]] = hist.get(r[0], 0) + 1
        if best is None or r[0] < best[0]:
            best = (r[0], al, be)
            print('j', j, '|C_j|', len(words), '|H|', r[0], 'alpha', al, 'beta', be)
            sys.stdout.flush()
    print('j', j, 'd', d, 'mode', mode, 'hist |H| of (E) levels', sorted(hist.items())[:12])


if __name__ == '__main__':
    main()
