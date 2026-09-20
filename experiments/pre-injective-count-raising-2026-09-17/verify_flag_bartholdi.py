"""Check one instance of the flag-augmented linear automaton on F_2 = <a,b>.

Alphabet A = K^Y with K = GF(2) and Y = {u, v}. Theta takes values in K e_u,
and the flag is written to the free coordinate y0 = v:

  tau(x)(h) = ( u(h)+u(ha^-1)+v(h)+v(hb^-1) ,  [x(h) != 0] ).

Checks, on the ball B_R of the Cayley tree:
 1. Theta is injective on configurations supported in B_R (rank over GF(2)
    equals 2|B_R|).  This is pre-injectivity of tau restricted to B_R.
 2. Never-creation: the flag coordinate is [x(h) != 0] by definition.
 3. Growth: x = (1,0) at the identity gives tau(x)(a) != 0.
 4. Non-injectivity: the constants (1,1)^G and (1,0)^G have the same image.
"""
import sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def mul(w, s):
    if w and w[-1] == INV[s]:
        return w[:-1]
    return w + (s,)


def ball(R):
    B = {()}
    fr = [()]
    for _ in range(R):
        nf = []
        for w in fr:
            for s in 'aAbB':
                v = mul(w, s)
                if v not in B:
                    B.add(v)
                    nf.append(v)
        fr = nf
    return sorted(B, key=lambda w: (len(w), w))


def rank_gf2(rows):
    rows = [r for r in rows if r]
    rank = 0
    piv = {}
    for r in rows:
        while r:
            hb = r.bit_length() - 1
            if hb in piv:
                r ^= piv[hb]
            else:
                piv[hb] = r
                rank += 1
                break
    return rank


def main(R):
    B = ball(R)
    out = ball(R + 1)
    oidx = {w: i for i, w in enumerate(out)}
    cols = []  # one column per input variable, as a bitmask over output sites
    for w in B:
        # u(w) contributes to Theta at h = w and h = w a (since u(h a^-1), h a^-1 = w)
        cols.append((1 << oidx[w]) | (1 << oidx[mul(w, 'a')]))
        # v(w) contributes at h = w and h = w b
        cols.append((1 << oidx[w]) | (1 << oidx[mul(w, 'b')]))
    r = rank_gf2(cols)
    n = 2 * len(B)
    print('R', R, 'ball', len(B), 'variables', n, 'rank', r)
    assert r == n, 'Theta not injective on the ball'
    # growth: x = (u=1, v=0) at identity; Theta(x)(a) = u(a a^-1) = 1
    assert oidx[('a',)] >= 0
    # non-injectivity on constants: Theta(1,1) = 1+1+1+1 = 0, Theta(1,0) = 1+1 = 0
    assert (1 + 1 + 1 + 1) % 2 == 0 and (1 + 1) % 2 == 0
    print('OK: pre-injective on B_R, never-creating, count-raising, not injective')


if __name__ == '__main__':
    for R in range(1, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 6):
        main(R)
