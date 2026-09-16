#!/usr/bin/env python3
"""Calibration of the transported certificate of primcert.py against the landed letter-once runs.

For every '-> PASS' line of lg_l15.out and lg_words16.out (the 30 + 70 classes certified by
lintongraph.py words, where the Magnus piece is free because an interior letter occurs once), redo
the class through the primcert.py pipeline: same zero-exponent basis (the recorded phi), canonical
Magnus sequence, Whitehead descent of W_0, isomorphism rho.phi : B_0 -> F(2), then
lintongraph.certify(2, A, B) on the transported data.  Two isomorphisms B_0 -> F(2) differ by an
automorphism of F(2), and every quantity of the certificate is invariant under automorphisms of
K = F(2) (and under psi <-> psi^-1 up to swapping the pair sZ), so the verdict, sorted sZ, depth,
|V|, H, t, hloops, tloops and the cycle flag must agree line by line.
Usage: calib.py LG_L15_OUT LG_WORDS16_OUT
"""
import sys, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import primcert as PC
C, LG, P = PC.C, PC.LG, PC.P


def transported(w, x, y):
    seq = C.magnus(C.adapt(list(w), x, y))
    cs = list(C.canon(seq))
    letters, g, W = P.piece(cs)
    if len(letters) != 3 or g != 1:
        return 'LEVELS', None
    Wm, phi = P.wh_descend(W, 3)
    if len(Wm) != 1:
        return 'NONPRIM', None
    img = P.apply(phi, W, cyclic=True)
    assert len(img) == 1
    xi = abs(img[0])
    assert PC.rose_check([phi[j] for j in (1, 2, 3)], 3)
    other = [j for j in (1, 2, 3) if j != xi]
    ren = {xi: [], other[0]: [1], other[1]: [2]}
    rho_phi = {h: P.apply(ren, phi[h]) for h in (1, 2, 3)}
    assert P.apply(rho_phi, W) == []
    return LG.certify(2, [tuple(rho_phi[1]), tuple(rho_phi[2])], [tuple(rho_phi[2]), tuple(rho_phi[3])])


def main():
    code = {'a': 1, 'A': -1, 't': 2, 'T': -2}
    pat = re.compile(r'VERDICT WORDS phi=(-?\d+),(-?\d+) (\S+) .* sZ=\((\d+), (\d+)\) depth=(\d+) '
                     r'mixed_nc=\d+ V=\[([^\]]*)\] H=(\d+) t=(\d+) hloops=(\d+) tloops=(\d+) '
                     r'cycle=(\w+) -> (\S+)')
    agree = disagree = 0
    for fn in sys.argv[1:]:
        for line in open(fn):
            if not line.rstrip().endswith('-> PASS'):
                continue
            m = pat.match(line)
            assert m, line
            x, y, wtxt = int(m.group(1)), int(m.group(2)), m.group(3)
            ref = (tuple(sorted((int(m.group(4)), int(m.group(5))))), int(m.group(6)),
                   len(m.group(7).split()), int(m.group(8)), int(m.group(9)), int(m.group(10)),
                   int(m.group(11)), m.group(12) == 'True', m.group(13))
            verdict, info = transported([code[ch] for ch in wtxt], x, y)
            if info is None:
                new = verdict
            else:
                new = (tuple(sorted(info['sZ'].values())) if isinstance(info.get('sZ'), dict)
                       else tuple(sorted(info.get('sZ'))), info.get('depth'), len(info.get('V', [])),
                       info.get('H'), info.get('t'), info.get('hloops'), info.get('tloops'),
                       bool(info.get('cycle')), verdict)
            ok = (new == ref)
            agree += ok
            disagree += (not ok)
            print('CAL %s %s ref=%s new=%s %s' % (os.path.basename(fn), wtxt, ref, new,
                                                   'AGREE' if ok else 'DISAGREE'), flush=True)
    print('COUNTS agree=%d disagree=%d' % (agree, disagree))
    print('SENTINEL_DONE', flush=True)


if __name__ == '__main__':
    main()
