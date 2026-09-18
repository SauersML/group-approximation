#!/usr/bin/env python3
"""Family C (the L14 frontier): structural checks behind the obstruction lemma of
research/malcev-root-steps-put-commutator-root-one-relators-in-h.md, and explicit poly-Z
targets for the first segment step.

For each relator (a/b/A/B letters) this prints
  * the Magnus rewrite r' in F(a_0, a_1, a_2) and its exponent vector, required (0, eps, 0);
  * kill-lo / kill-hi: r'(1, y, z) and r'(x, y, 1) reduced cyclically, required to be y^k,
    k != 0 (this is the 'propagation' hypothesis: in a torsion-free target, a dead letter
    of the segment kills its neighbours);
  * edges: r' = a_2^-1 x a_2 y cyclically (the top letter occurs exactly twice), so
    S_[0,n] is the HNN extension of S_[0,n-1] with stable letter a_{n+2} along <x_n> -> <y_n^-1>
    (x_n, y_n: x, y shifted by n);
  * sol: a homomorphism from S_[0,1] = <a_0..a_3 | r'(a_0,a_1,a_2), r'(a_1,a_2,a_3)> to a
    poly-Z group Z^2 x|_B Z under which x_0, y_0, x_1, y_1 are all nontrivial (so both steps
    S_[0,-1] -> S_[0,0] -> S_[0,1] are climbed by the edge-injective quotient lemma with this
    non-residually-nilpotent torsion-free target; cyclic edge groups, so nontrivial = injective),
    or 'none found'.

Usage: frontier_check.py WORD ...
"""
import itertools, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "perfect-kernel-segment-targets-2026-09-17"))
import retract_segment_certify as rsc  # noqa: E402
hc, sc = rsc.hc, rsc.sc


def P(s):
    return tuple((0 if c in "aA" else 1, 1 if c.islower() else -1) for c in s)


def magnus(s):
    w = hc.canon(hc.cred(P(s)))
    if 0 not in hc.exps(w).values():
        w = hc.nielsen_zero(w)   # the same Nielsen move the certifier makes
    e = hc.exps(w)
    for t in [a for a in e if e[a] == 0]:
        r = hc.rewrite(w, t)
        lo = min(p for (_, p), _ in r)
        r = tuple(((0, p - lo), x) for (_, p), x in r)
        m = max(p for (_, p), _ in r)
        ev = [0] * (m + 1)
        for (_, p), x in r:
            ev[p] += x
        if m == 2 and ev[0] == 0 and ev[2] == 0 and ev[1] != 0:
            return r, ev
    return None, None


def kill(r, p):
    w = hc.cred(tuple(x for x in r if x[0][1] != p))
    ok = len({a for a, _ in w}) == 1 and len({e for _, e in w}) == 1
    return ok, sc.show(w)


# ------------------------------------------------ Z^2 x|_B Z, elements (v, n)
def mat_mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def mat_pow(B, n):
    Bi = [[B[1][1], -B[0][1]], [-B[1][0], B[0][0]]]
    det = B[0][0] * B[1][1] - B[0][1] * B[1][0]
    Bi = [[x * det for x in row] for row in Bi]  # inverse, det = +-1
    M = [[1, 0], [0, 1]]
    for _ in range(abs(n)):
        M = mat_mul(M, B if n > 0 else Bi)
    return M


def act(M, v):
    return (M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1])


def mul(B, g, h):
    (v, n), (w, m) = g, h
    x = act(mat_pow(B, n), w)
    return ((v[0] + x[0], v[1] + x[1]), n + m)


def ginv(B, g):
    v, n = g
    x = act(mat_pow(B, -n), v)
    return ((-x[0], -x[1]), -n)


def evalw(B, r, imgs, shift):
    g = ((0, 0), 0)
    for (_, p), e in r:
        h = imgs[p + shift]
        g = mul(B, g, h if e == 1 else ginv(B, h))
    return g


ENDV = [(0, 0), (1, 0), (0, 1)]
MATS = [[[3, 4], [2, 3]], [[3, 2], [4, 3]], [[-1, 0], [0, -1]], [[2, 1], [1, 1]], [[-3, -4], [-2, -3]]]


def edges(r):
    """(x, y) with r = a_2^-1 x a_2 y cyclically, or None if a_2 does not occur exactly twice."""
    idx = [i for i, ((_, p), _) in enumerate(r) if p == 2]
    if len(idx) != 2:
        return None
    n = len(r)
    i = next(j for j in idx if r[j][1] == -1)
    w = r[i:] + r[:i]
    j = next(k for k in range(1, n) if w[k][0][1] == 2)
    return w[1:j], w[j + 1:]


def sol_target(r):
    one = ((0, 0), 0)
    xy = edges(r)
    if xy is None:
        return "no cyclic edge"
    vecs = [v for v in itertools.product(range(-2, 3), repeat=2)]
    for B in MATS:
        for n0, n3 in itertools.product((-1, 1, -2, 2), repeat=2):
            for v1 in ((1, 0), (0, 1), (1, 1), (1, -1)):
                for v2 in vecs:
                    if v2 == (0, 0):
                        continue
                    for u0 in ENDV:
                        for u3 in ENDV:
                            imgs = [(u0, n0), (v1, 0), (v2, 0), (u3, n3)]
                            if evalw(B, r, imgs, 0) == one and evalw(B, r, imgs, 1) == one and all(
                                    evalw(B, e, imgs, sh) != one for e in xy for sh in (0, 1)):
                                return "B=%s a0=%s a1=%s a2=%s a3=%s" % (B, imgs[0], imgs[1], imgs[2], imgs[3])
    return "none found"


def main():
    for s in sys.argv[1:]:
        r, ev = magnus(s)
        if r is None:
            print(s, "not of family-C shape")
            continue
        klo, khi = kill(r, 0), kill(r, 2)
        print("%-15s r'=%-18s e=%s kill-lo=%s(%s) kill-hi=%s(%s) sol: %s" % (
            s, sc.show(r), ev, klo[1], klo[0], khi[1], khi[0], sol_target(r)))


if __name__ == "__main__":
    main()
