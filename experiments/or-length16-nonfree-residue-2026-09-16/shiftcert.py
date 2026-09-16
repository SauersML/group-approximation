#!/usr/bin/env python3
"""Second pass over the classes left by primcert.py: other zero-exponent bases.

After census.adapt the relator w has t-exponent sum 0.  For k in -KMAX..KMAX the Nielsen move
t -> t a^k keeps the t-exponent sum 0 (so it is again a zero-exponent basis for the same group)
and changes the interior a-syllables of the Magnus rewriting.  For each image: cyclically
reduce, take census.magnus / census.canon, form W_0, run the Whitehead descent, and when W_0 is
primitive with 3 levels and level gcd 1, run the same certificate as primcert.py.
Usage: shiftcert.py PRIMCERT_OUT KMAX
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import primcert as PC
C, LG, P = PC.C, PC.LG, PC.P


def certify_word(w):
    """w: cyclically reduced word, t-exponent sum 0.  Returns (tag, text)."""
    seq = C.magnus(w)
    if seq is None:
        return 'NOSEQ', ''
    cs = list(C.canon(seq))
    m, n, g, top, bot = C.extremes(cs)
    if C.peelable(top) or C.peelable(bot):
        return 'PEEL', ''
    letters, g, W = P.piece(cs)
    if len(letters) != 3 or g != 1:
        return 'LEVELS', 'levels=%d g=%d' % (len(letters), g)
    Wm, phi = P.wh_descend(W, 3)
    if len(Wm) != 1:
        return 'NONPRIM', 'W0=%s whmin=%d' % (P.wstr(W), len(Wm))
    img = P.apply(phi, W, cyclic=True)
    assert len(img) == 1
    xi = abs(img[0])
    assert PC.rose_check([phi[j] for j in (1, 2, 3)], 3)
    other = [j for j in (1, 2, 3) if j != xi]
    ren = {xi: [], other[0]: [1], other[1]: [2]}
    rho_phi = {h: P.apply(ren, phi[h]) for h in (1, 2, 3)}
    assert P.apply(rho_phi, W) == []
    Agens = [tuple(rho_phi[1]), tuple(rho_phi[2])]
    Bgens = [tuple(rho_phi[2]), tuple(rho_phi[3])]
    verdict, info = LG.certify(2, Agens, Bgens)
    V = ' '.join('%s:%s' % (p, LG.wstr(nn, 2)) for p, nn in info.get('V', []))
    txt = ('W0=%s kill=x%d A=[%s,%s] B=[%s,%s] rankA=%s rankB=%s sZ=%s depth=%s mixed_nc=%s V=[%s] '
           'H=%s t=%s hloops=%s tloops=%s cycle=%s -> %s'
           % (P.wstr(W), xi, LG.wstr(Agens[0], 2), LG.wstr(Agens[1], 2), LG.wstr(Bgens[0], 2),
              LG.wstr(Bgens[1], 2), info.get('rankA'), info.get('rankB'), info.get('sZ'),
              info.get('depth'), info.get('mixed_noncyclic'), V, info.get('H'), info.get('t'),
              info.get('hloops'), info.get('tloops'), bool(info.get('cycle')), verdict))
    return verdict, txt


def main():
    kmax = int(sys.argv[2])
    code = {'a': 1, 'A': -1, 't': 2, 'T': -2}
    todo = []
    for line in open(sys.argv[1]):
        f = line.split()
        if f and f[0] == 'NONPRIM':
            todo.append(f[1])
        elif f and f[0] == 'VERDICT' and not line.rstrip().endswith('-> PASS'):
            todo.append(f[2])
    print('TODO %d' % len(todo), flush=True)
    counts = {}
    for wtxt in todo:
        w = [code[ch] for ch in wtxt]
        (x, y), = P.phis_for(w)
        w0 = C.adapt(list(w), x, y)
        assert C.expsums(w0)[1] == 0
        done = None
        tags = []
        for k in sorted(range(-kmax, kmax + 1), key=abs):
            wk = C.cyc_reduce(C.subst(w0, {1: [1], 2: [2] + C.power(1, k)}))
            assert C.expsums(wk)[1] == 0
            tag, txt = certify_word(wk)
            tags.append('%d:%s' % (k, tag))
            if tag.startswith('PASS') or tag.startswith('FAIL'):
                print('VERDICT SHIFT %s k=%d image=%s %s' % (wtxt, k, C.word_str(wk), txt), flush=True)
            if tag == 'PASS':
                done = k
                break
        res = 'PASS' if done is not None else 'OPEN'
        counts[res] = counts.get(res, 0) + 1
        print('RESULT %s %s tags=%s' % (wtxt, res, ','.join(tags)), flush=True)
    print('COUNTS %s' % sorted(counts.items()))
    print('SENTINEL_DONE', flush=True)


if __name__ == '__main__':
    main()
