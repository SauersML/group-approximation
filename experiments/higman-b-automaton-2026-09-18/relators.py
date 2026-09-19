"""Twisted relators S_beta = beta . R (beta in Bbar_e) from the self-similar model, for e <= 8.

beta acts on the vertex R = (x_1..x_8) = (-1,-1,1,1,-1,-1,1,1) by
    x_i -> x_i * T^(s(mu_(i-1))),  mu_0 = beta,  mu_i = section of mu_(i-1) at the letter x_i,
where s(g) is the first-letter exponent of g (g multiplies the first letter by T^s).
Under (H_e) (hcheck.py), Abar_e = < a, c | a^m, c^m, S_beta (beta in Bbar) >.
Writes abar_e<e>.g with TwistRels(F) (distinct up to rotation and inversion) and cross-checks
S_(b d) against hfail-output.txt of w13 (e = 7, 8).
usage: python3 relators.py e
"""
import sys
e = int(sys.argv[1])
sys.argv = [sys.argv[0], str(e), '4']
import levels
Rb, Rd, elems, sizes = levels.build(4, verbose=False)
assert sizes[-1] == sizes[-2]
m, M, T = levels.m, levels.M, levels.T
R = [(-1) % m, (-1) % m, 1, 1, (-1) % m, (-1) % m, 1, 1]
def image(g):
    out = []
    for x in R:
        s = elems[g][0]
        out.append(x * pow(T, s, m) % m)
        g = elems[g][1 + x % M]
    return tuple(out)
def canon(w):
    """cyclic word of alternating a/c syllables (length 8, a first): least rotation by 2 / inversion."""
    best = None
    L = len(w)
    for u in (w, tuple((-x) % m for x in reversed(w))):
        # inversion of a^x1 c^x2 ... c^x8 is c^-x8 ... a^-x1: rotate by one to start with a
        if u is not w: u = u[1:] + u[:1]
        for i in range(0, L, 2):
            c = u[i:] + u[:i]
            if best is None or c < best: best = c
    return best
N = len(elems)
rels = set(image(g) for g in range(N))
crels = set(canon(w) for w in rels)
bd = Rd[Rb[0]]
print("e=%d |Bbar|=%d distinct S_beta=%d, up to rotation/inversion=%d" % (e, N, len(rels), len(crels)))
print("S_(b d) =", image(bd))
def gw(w):
    return '*'.join('%s^%d' % ('ac'[i % 2], x if x <= m // 2 else x - m) for i, x in enumerate(w))
with open('abar_e%d.g' % e, 'w') as f:
    f.write('# relators.py %d: S_beta for all %d beta in Bbar, %d up to rotation/inversion\n' % (e, N, len(crels)))
    f.write('TwistRels:=function(F) local a,c; a:=F.1; c:=F.2; return [\n' + ',\n'.join(gw(w) for w in sorted(crels)) + ']; end;;\n')
