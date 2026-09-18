"""Linton certificate for relators whose Magnus piece W_0(a_0,a_1,a_2) is primitive but not
visibly free (no interior letter occurring once).  Whitehead-minimise W_0 while tracking the
automorphism phi of F(a_0,a_1,a_2); phi(W_0) = c^{+-1} gives B_0 = F_3/<<c>> = F(other two
letters), the images of a_0,a_1,a_2 are phi(a_i) with c deleted, and
    G = K *_psi,  K = B_0,  A = <a_0,a_1>,  B = <a_1,a_2>,  psi(a_0)=a_1, psi(a_1)=a_2.
Then lintongraph.certify (K free of rank 2) is run.  Usage: linfree.py pieces19.out"""
import sys
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/or-unpeelable-census-scripts-2026-09-12')
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/one-relator-linton-graph-certificates-scripts')
import lintongraph as LG
from whitehead import fr, cr, wh_auts


def app(w, a, S, cyc):
    """Whitehead automorphism (a, S): x -> a^-1 x if x^-1 in S, x -> x a if x in S."""
    o = []
    for x in w:
        if x in (a, -a):
            o.append(x)
            continue
        o.extend(([-a] if (-x) in S else []) + [x] + ([a] if x in S else []))
    return cr(o) if cyc else fr(o)


def whmin_track(W, r=3):
    w = cr(W)
    img = {g: [g] for g in range(1, r + 1)}
    auts = list(wh_auts(r))
    imp = True
    while imp:
        imp = False
        for a, S in auts:
            v = app(w, a, S, True)
            if len(v) < len(w):
                w = v
                img = {g: app(img[g], a, S, False) for g in img}
                imp = True
                break
    return w, img


def image(W, img):
    return fr([y for x in W for y in (img[x] if x > 0 else [-z for z in reversed(img[-x])])])


def run(W):
    m, img = whmin_track(W)
    if len(m) != 1:
        return 'NONFREE', None
    c = abs(m[0])
    im_w = cr(image(W, img))
    assert len(im_w) == 1 and abs(im_w[0]) == c, 'tracked automorphism does not send W_0 to c'
    others = [g for g in (1, 2, 3) if g != c]
    rel = {others[0]: 1, others[1]: 2}
    im = {g: tuple(fr([(rel[abs(x)] if x > 0 else -rel[abs(x)]) for x in img[g] if abs(x) != c]))
          for g in img}
    v, info = LG.certify(2, [im[1], im[2]], [im[2], im[3]])
    return v, (info, im)


if __name__ == '__main__':
    xyz = {'x': 1, 'X': -1, 'y': 2, 'Y': -2, 'z': 3, 'Z': -3}
    for line in open(sys.argv[1]):
        f = line.split()
        if not f or f[-1] != 'FREE':
            continue
        W = [xyz[ch] for ch in f[2]]
        v, rest = run(W)
        if rest is None:
            print('NONFREE', f[0])
            continue
        info, im = rest
        print('LINFREE %s W0=%s a0=%s a1=%s a2=%s sZ=%s |V|=%d H=%s t=%s hloops=%s tloops=%s cycle=%s -> %s' % (
            f[0], f[2], LG.wstr(im[1], 2), LG.wstr(im[2], 2), LG.wstr(im[3], 2), info.get('sZ'),
            len(info.get('V', [])), info.get('H'), info.get('t'), info.get('hloops'),
            info.get('tloops'), bool(info.get('cycle')), v), flush=True)
    print('SENTINEL_DONE')
