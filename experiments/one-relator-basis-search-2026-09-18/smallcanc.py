"""Small cancellation test for a one-relator presentation <a,t | w>, w cyclically reduced.
Symmetrised set R* = all cyclic conjugates of w and w^-1.
 maxpiece: longest word that is a common prefix of two distinct elements of R*.
 C'(1/6): maxpiece < |w|/6;  C'(1/4): maxpiece < |w|/4.
 T(4) (Lyndon--Schupp, Ch. V.2): no r1,r2,r3 in R* with r1 != r2^-1, r2 != r3^-1, r3 != r1^-1
 such that each of r1r2, r2r3, r3r1 has cancellation (last letter of r_i inverse to first of r_{i+1}).
Usage: smallcanc.py FILE (relator = first field)."""
import sys
inv = {'a': 'A', 'A': 'a', 't': 'T', 'T': 't'}
def I(w): return ''.join(inv[c] for c in reversed(w))
def cyc_red(w):
    for i in range(len(w)):
        assert w[i] != inv[w[(i + 1) % len(w)]], 'not cyclically reduced'
def analyse(w):
    cyc_red(w)
    L = len(w)
    R = sorted(set([w[i:] + w[:i] for i in range(L)] + [I(w)[i:] + I(w)[:i] for i in range(L)]))
    assert len(R) == 2 * L, 'relator is a proper power or conjugate to its inverse'
    mp = 0
    for i, u in enumerate(R):
        for v in R[i + 1:]:
            k = 0
            while k < L and u[k] == v[k]: k += 1
            mp = max(mp, k)
    Rs = set(R)
    t4 = True
    wit = None
    for r1 in R:
        for r2 in R:
            if r2 == I(r1) or r1[-1] != inv[r2[0]]: continue
            for r3 in R:
                if r3 == I(r2) or r1 == I(r3): continue
                if r2[-1] == inv[r3[0]] and r3[-1] == inv[r1[0]]:
                    t4 = False; wit = (r1, r2, r3); break
            if not t4: break
        if not t4: break
    return L, mp, t4, wit
if __name__ == '__main__':
    for line in open(sys.argv[1]):
        f = line.split()
        if not f: continue
        w = f[0]
        L, mp, t4, wit = analyse(w)
        c6, c4 = 6 * mp < L, 4 * mp < L
        verdict = "C'(1/6)" if c6 else ("C'(1/4)-T(4)" if (c4 and t4) else ("C'(1/4) only" if c4 else 'none'))
        print('SC %s len=%d maxpiece=%d C6=%s C4=%s T4=%s -> %s%s' % (w, L, mp, c6, c4, t4, verdict,
              '' if t4 else ' T4witness=%s,%s,%s' % wit), flush=True)
    print('SENTINEL_DONE')
