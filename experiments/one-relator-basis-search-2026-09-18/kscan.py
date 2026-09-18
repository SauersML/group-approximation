"""Out(F_2)=GL_2(Z): up to inner automorphisms and signs, the bases of F(a,t) in which t still has
exponent sum 0 (a having exponent sum +-1) are t -> t a^k.  Scan k and test the Magnus piece."""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import basis_search as BS
from whitehead import cr
for line in open(sys.argv[1]):
    f = line.split()
    if not f: continue
    rel = f[-1] if f[0] == 'REST' else f[0]
    w = [BS.CH[c] for c in rel]
    out = []
    for k in range(-int(sys.argv[2]), int(sys.argv[2]) + 1):
        wp = BS.subst(w, {1: [1], 2: [2] + [1] * k if k >= 0 else [2] + [-1] * (-k)})
        n, W0 = BS.magnus(wp, 2)
        v, ml, rest = BS.test_piece(n, W0)
        out.append('%d:%s%s' % (k, v if rest else 'NF', '' if rest else '(wh%d/%d)' % (ml, len(W0))))
    print('KSCAN', rel, ' '.join(out), flush=True)
print('SENTINEL_DONE')
