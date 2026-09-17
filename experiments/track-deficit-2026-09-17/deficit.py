"""Exact decoder deficits of star designs 6, 6c and 7 over the free group F_2 = <a, b>.

Supports research/rest-count-preservation-from-charge-noncreation.md (lane (b) of
notes/agent-coordination-playbook-2026-09-17.md, "track deficit as an information-transport index").

Alphabet A = (Z/2)^2 with vacuum 0 = (0, 0). Reversible automata tau on A^G (all fix 0^G):
  id      tau x = x
  shift   tau x(g) = x(g a)                      inverse x(g A)
  shear   tau (u, v)(g) = (u(g), v(g) + u(g a) u(g b))   (an involution)
  ssw     shear o swap o shear, swap (u, v) -> (v, u) sitewise
Designs (notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md, Section 5):
  D6   on (A + {*})^G:  x -> tau(F x) off the star set Z, * on Z; F fills stars by 0.
  D6c  creation variant: keep tau(Fx)(g) if x(g) in A or tau(Fx)(g) != 0, else write *.
  D7   on (A x A)^G:  R(u, v) = (tau(sigma u + v 1_N(u)), v 1_(G - N(u))), sigma = tau^-1,
       N(u) = {g : u(g) = 0}.
For a finite window W we take x uniform among configurations whose non-vacuum part lies in W
(non-star part for D6, D6c) and print the exact conditional entropy H(x | Phi x) in bits,
plus the number of colliding outputs. Deficit 0 means Phi is injective on that window.

Checks printed:
  (1) the deficit is not invariant under composing tau with a reversible automaton
      (id versus shift in D6), so shape (1) of lane (b) fails;
  (2) the deficit is not log2|A| per anything: shear in D6 gives 0 although tau moves material;
  (3) shear both raises and lowers the count |x| (so it is outside the target claim's hypothesis);
  (4) D6c is injective on the window exactly when tau never creates at a vacuum site there.
"""
import itertools, math
from collections import Counter

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}

def mul(g, h):
    out = list(g)
    for c in h:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)

ZERO = (0, 0)
SYMS = [(i, j) for i in (0, 1) for j in (0, 1)]

class CA:
    def __init__(self, memory, rule, vac=ZERO):
        self.M, self.rule, self.vac = memory, rule, vac
    def __call__(self, x):
        cand = {mul(s, INV_WORD(m)) for s in x for m in self.M} | set(x)
        y = {}
        for g in cand:
            val = self.rule(tuple(x.get(mul(g, m), self.vac) for m in self.M))
            if val != self.vac:
                y[g] = val
        return y

def INV_WORD(w):
    return ''.join(INV[c] for c in reversed(w))

def compose(*cas):  # compose(f, g)(x) = f(g(x))
    class C:
        def __call__(self, x):
            for c in reversed(cas):
                x = c(x)
            return x
    return C()

ID = CA([''], lambda t: t[0])
SHIFT = CA(['a'], lambda t: t[0])
SHIFT_INV = CA(['A'], lambda t: t[0])
SHEAR = CA(['', 'a', 'b'], lambda t: (t[0][0], t[0][1] ^ (t[1][0] & t[2][0])))
SWAP = CA([''], lambda t: (t[0][1], t[0][0]))
SSW = compose(SHEAR, SWAP, SHEAR)
SSW_INV = compose(SHEAR, SWAP, SHEAR)  # each factor is an involution, and the word is a palindrome
TAUS = {'id': (ID, ID), 'shift': (SHIFT, SHIFT_INV), 'shear': (SHEAR, SHEAR), 'ssw': (SSW, SSW_INV)}

def key(y):
    return frozenset(y.items())

def cond_entropy(outputs):
    n = len(outputs)
    cnt = Counter(outputs)
    return sum(c * math.log2(c) for c in cnt.values()) / n, sum(1 for c in cnt.values() if c > 1)

STAR = '*'

def D6(tau, x):  # x: dict over window sites with values in SYMS or STAR (outside window: star)
    fx = {g: s for g, s in x.items() if s != STAR and s != ZERO}
    t = tau(fx)
    return key({g: t.get(g, ZERO) for g, s in x.items() if s != STAR})

def D6c(tau, x, window):
    fx = {g: s for g, s in x.items() if s != STAR and s != ZERO}
    t = tau(fx)
    out = {}
    for g, s in t.items():  # sites outside the window are stars of x; a creation there is kept
        if g not in x:
            out[g] = s
    for g, s in x.items():
        v = t.get(g, ZERO)
        if s != STAR or v != ZERO:
            out[g] = v
    return key(out)

def creates_at_vacuum(tau, x):
    fx = {g: s for g, s in x.items() if s != STAR and s != ZERO}
    t = tau(fx)
    return any(g not in fx and g in t for g in t)

def D7(tau, sigma, u, v):
    su = sigma(u)
    first = dict(su)
    for g, s in v.items():
        if g not in u:  # u(g) = 0, so g in N(u)
            val = tuple(p ^ q for p, q in zip(first.get(g, ZERO), s))
            if val == ZERO:
                first.pop(g, None)
            else:
                first[g] = val
    p = tau(first)
    q = {g: s for g, s in v.items() if g in u}
    return key(p), key(q)

W3 = ['', 'a', 'b']
B1 = ['', 'a', 'A', 'b', 'B']
W4 = ['', 'a', 'b', 'ab']

def configs(window, syms):
    for vals in itertools.product(syms, repeat=len(window)):
        yield {g: s for g, s in zip(window, vals)}

def main():
    # reversibility sanity check on B1-supported configurations
    for name, (t, ti) in TAUS.items():
        for x in configs(B1, SYMS):
            x = {g: s for g, s in x.items() if s != ZERO}
            assert ti(t(x)) == x, name
    print("reversibility of id, shift, shear, ssw verified on all 4^5 configurations supported in the unit ball")

    print("\nD6 and D6c: uniform x in (A + {*})^W, stars outside W; H(x | Phi x) in bits, colliding outputs")
    for wname, win in (('{e,a,b}', W3), ('ball(1)', B1)):
        for name, (t, _) in TAUS.items():
            xs = list(configs(win, SYMS + [STAR]))
            h6, c6 = cond_entropy([D6(t, x) for x in xs])
            h6c, c6c = cond_entropy([D6c(t, x, win) for x in xs])
            cr = sum(1 for x in xs if creates_at_vacuum(t, x))
            print(f"  W={wname:8} tau={name:6} D6: H={h6:.4f} coll={c6:5d}   D6c: H={h6c:.4f} coll={c6c:5d}   "
                  f"inputs where tau(Fx) creates at a vacuum site: {cr}")
            if cr == 0:
                assert h6c == 0
    print("\nD7: uniform (u, v) in (A x A)^W supported in W; H((u,v) | R(u,v)) in bits, colliding outputs")
    for wname, win in (('{e,a}', ['', 'a']), ('{e,a,b}', W3), ('{e,a,b,ab}', W4)):
        for name, (t, ti) in TAUS.items():
            outs = []
            for pairs in itertools.product(itertools.product(SYMS, SYMS), repeat=len(win)):
                u = {g: p[0] for g, p in zip(win, pairs) if p[0] != ZERO}
                v = {g: p[1] for g, p in zip(win, pairs) if p[1] != ZERO}
                outs.append(D7(t, ti, u, v))
            h7, c7 = cond_entropy(outs)
            print(f"  W={wname:11} tau={name:6} D7: H={h7:.4f} coll={c7:6d}  (log2|A| = 2)")

    print("\ncount changes of shear on finite configurations")
    x_up = {'a': (1, 0), 'b': (1, 0)}
    y = SHEAR(x_up)
    print(f"  x = (1,0) at a, b:  |x| = {len(x_up)}, |shear x| = {len(y)}")
    x_dn = y
    print(f"  x = shear of that:  |x| = {len(x_dn)}, |shear x| = {len(SHEAR(x_dn))}")
    assert len(y) > len(x_up) and len(SHEAR(x_dn)) < len(x_dn)

if __name__ == '__main__':
    main()
