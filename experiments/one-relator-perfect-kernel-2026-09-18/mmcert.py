"""Second-level certificate for a non-free Magnus piece B_0 = <x,y,z | W_0>.
Magnus--Moldavanskii rewriting of W_0 with respect to a letter s of exponent sum 0 gives
    B_0 = V *_psi,  V = <u_i (u in the two other letters, m_u <= i <= M_u) | R>,
    A = <u_i : m_u <= i < M_u>,  B = <u_i : m_u < i <= M_u>,  psi(u_i) = u_(i+1).
If R is primitive (Whitehead-minimal length 1), V is free of rank r-1 on the tracked basis and
lintongraph.certify is run on (V, A, B, psi).  PASS (with rank A = rank B <= 2, strongly inert) means the length-one
hierarchy of B_0 is Z-stable and B_0 contains no Baumslag--Solitar subgroup, i.e. hypothesis (QC)
of quasiconvex-hierarchy-piece-nonsingular-extremes-sofic for the piece.
Usage: mmcert.py pieces19.out"""
import sys
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/or-unpeelable-census-scripts-2026-09-12')
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/one-relator-linton-graph-certificates-scripts')
import lintongraph as LG
from whitehead import fr, cr
from linfree import whmin_track, image


def rewrite(W0, s):
    h, out = 0, []
    for ch in W0:
        if ch.lower() == s:
            h += 1 if ch == s else -1
        else:
            out.append((ch, h))
    if h != 0:
        return None
    m = min(hh for _, hh in out)
    return [(c, hh - m) for c, hh in out]


def certify_piece(W0):
    res = []
    for s in 'xyz':
        if W0.count(s) != W0.count(s.upper()) or s not in W0.lower():
            continue
        R = rewrite(W0, s)
        lets = sorted(set(c.lower() for c, _ in R))
        rng = {u: (min(h for c, h in R if c.lower() == u), max(h for c, h in R if c.lower() == u)) for u in lets}
        gens = [(u, i) for u in lets for i in range(rng[u][0], rng[u][1] + 1)]
        idx = {g: k + 1 for k, g in enumerate(gens)}
        r = len(gens)
        Rw = [idx[(c.lower(), h)] * (1 if c.islower() else -1) for c, h in R]
        m, img = whmin_track(Rw, r)
        Astr = ' '.join('%s%d' % g for g in gens if g[1] < rng[g[0]][1])
        Rs = ' '.join('%s%d' % (c, h) for c, h in R)
        if len(m) != 1:
            res.append((s, Rs, 'VERTEX-NONFREE(whmin len %d)' % len(m), None))
            continue
        c = abs(m[0])
        im_w = cr(image(Rw, img))
        assert len(im_w) == 1 and abs(im_w[0]) == c
        others = [g for g in range(1, r + 1) if g != c]
        rel = {o: k + 1 for k, o in enumerate(others)}
        im = {g: tuple(fr([(rel[abs(x)] if x > 0 else -rel[abs(x)]) for x in img[g] if abs(x) != c]))
              for g in img}
        Ag = [im[idx[(u, i)]] for (u, i) in gens if i < rng[u][1]]
        Bg = [im[idx[(u, i + 1)]] for (u, i) in gens if i < rng[u][1]]
        if not 1 <= len(Ag) <= 2:
            res.append((s, Rs, 'EDGE-RANK-%d(not covered by rank-two inertness)' % len(Ag), None))
            continue
        v, info = LG.certify(r - 1, Ag, Bg)
        res.append((s, Rs, v, info))
        if v == 'PASS':
            break
    return res


if __name__ == '__main__':
    for line in open(sys.argv[1]):
        f = line.split()
        if not f or f[-1] != 'NONFREE':
            continue
        for s, Rs, v, info in certify_piece(f[2]):
            extra = ''
            if info:
                extra = ' sZ=%s |V|=%d H=%s t=%s hloops=%s tloops=%s cycle=%s' % (
                    info.get('sZ'), len(info.get('V', [])), info.get('H'), info.get('t'),
                    info.get('hloops'), info.get('tloops'), bool(info.get('cycle')))
            print('MMCERT %s W0=%s stable=%s R=[%s]%s -> %s' % (f[0], f[2], s, Rs, extra, v), flush=True)
    print('SENTINEL_DONE')
