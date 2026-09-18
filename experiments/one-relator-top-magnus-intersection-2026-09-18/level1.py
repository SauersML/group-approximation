"""Level-1 Z-stability of the Magnus piece B_0 = <a_0..a_n | W_0> of G = <a,t | w>, any edge rank.
For each letter s of W_0 with exponent sum 0: rewrite W_0 along s, B_0 = V *_psi with
V = <u_i : u != s, m_u <= i <= M_u | R>, A = <u_i : i < M_u>, B = <u_i : i > m_u>, psi(u_i) = u_(i+1).
If R is primitive (Whitehead-minimal length 1), V is free on the tracked basis, and
lintongraph.certify computes the pure-direction stabiliser classes of Linton's definition (p. 23)
by Stallings pullbacks and returns sZ(psi), sZ(psi^-1) when they are finite (else a depth-cap FAIL).
Only the sZ values are used here: the graph-of-cyclic-stabilisers verdict (which needs no BS) is
replaced by hyperbolicity of G (kbhyp.sh).  Output: L1 w s rank(A) sZ=(f,b) or the failure."""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import magint as MI
LG, fr = MI.LG, MI.fr


def level1(w):
    n, W0 = MI.magnus(w, 2)
    out = []
    for s in range(1, n + 2):
        R = MI.rewrite_raw(W0, s)
        if R is None:
            out.append((s, 'S-EXP-NONZERO', None))
            continue
        lets = sorted(set(u for u, _, _ in R))
        rng = {u: (min(h for v, h, _ in R if v == u), max(h for v, h, _ in R if v == u)) for u in lets}
        gens = [(u, i) for u in lets for i in range(rng[u][0], rng[u][1] + 1)]
        idx = {g: k + 1 for k, g in enumerate(gens)}
        r = len(gens)
        Rw = [idx[(u, h)] * e for u, h, e in R]
        m, img = MI.whmin_track(Rw, r)
        if len(m) != 1:
            out.append((s, 'VERTEX-NONFREE(%d)' % len(m), None))
            continue
        c = abs(m[0])
        others = [g for g in range(1, r + 1) if g != c]
        rel = {o: k + 1 for k, o in enumerate(others)}
        im = {g: tuple(fr([(rel[abs(x)] if x > 0 else -rel[abs(x)]) for x in img[idx[g]] if abs(x) != c]))
              for g in gens}
        Ag = [im[(u, i)] for (u, i) in gens if i < rng[u][1]]
        Bg = [im[(u, i + 1)] for (u, i) in gens if i < rng[u][1]]
        if not Ag:
            out.append((s, 'EDGE-TRIVIAL', None))
            continue
        v, info = LG.certify(r - 1, Ag, Bg, dmax=12)
        out.append((s, 'rankA=%d sZ=%s lg=%s' % (len(Ag), info.get('sZ'), v), info.get('sZ')))
    return n, W0, out


if __name__ == '__main__':
    for line in open(sys.argv[1]):
        f = line.split()
        if not f:
            continue
        w = [MI.CH[c] for c in f[0]]
        n, W0, out = level1(w)
        ok = [s for s, _, sz in out if sz is not None]
        print('L1 %s %s -> %s' % (f[0], ' '.join('[s=a%d %s]' % (s - 1, t) for s, t, _ in out),
                                  ('ZSTABLE via s=a%d' % (ok[0] - 1)) if ok else 'UNCERTIFIED'), flush=True)
    print('SENTINEL_DONE')
