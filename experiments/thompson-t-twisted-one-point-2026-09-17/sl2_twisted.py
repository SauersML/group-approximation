"""Exact twisted solutions in SL(2, q): a^4 = -1, b^3 = 1, (ba)^5 = 1, and which of r_1, r_2 hold.

A pair (a, b) in SL(2, q) with a^4 = -I, b^3 = I, (ba)^5 = I generates a finite group H containing -I.
Every complex irreducible representation of H in which -I acts by -1 gives an EXACT pair (U, V) with
U^4 = -1, V^3 = 1, (VU)^5 = 1, and r_i(U, V) = 1 whenever r_i(a, b) = I in H.
So r_1(a, b) = I shows that the twisted defect with r_2 dropped vanishes in the degree of such an irrep,
and likewise for r_2. (Both cannot be I: that would give a finite image of C_T(J) with J -> -1.)

Fields: F_p for odd primes p, and F_9 = F_3[i], i^2 = -1, F_25 = F_5[s], s^2 = 2, F_49 = F_7[i].
Output: for each q, the counts of (a, b) with each (r_1, r_2) outcome in {I, -I, other}, over a fixed
a per conjugacy class of elements with a^4 = -I, and b over all elements of order 3.
"""
import itertools
import json
import sys


class Fq:
    """F_p or F_p[t]/(t^2 - nr) with nr a non-residue."""

    def __init__(self, p, nr=None):
        self.p, self.nr = p, nr
        if nr is None:
            self.els = [(x, 0) for x in range(p)]
        else:
            self.els = [(x, y) for x in range(p) for y in range(p)]

    def add(self, u, v):
        return ((u[0] + v[0]) % self.p, (u[1] + v[1]) % self.p)

    def neg(self, u):
        return ((-u[0]) % self.p, (-u[1]) % self.p)

    def mul(self, u, v):
        p = self.p
        if self.nr is None:
            return ((u[0] * v[0]) % p, 0)
        return ((u[0] * v[0] + self.nr * u[1] * v[1]) % p, (u[0] * v[1] + u[1] * v[0]) % p)


def make(F):
    Z, O = (0, 0), (1, 0)

    def mm(A, B):
        return (
            F.add(F.mul(A[0], B[0]), F.mul(A[1], B[2])),
            F.add(F.mul(A[0], B[1]), F.mul(A[1], B[3])),
            F.add(F.mul(A[2], B[0]), F.mul(A[3], B[2])),
            F.add(F.mul(A[2], B[1]), F.mul(A[3], B[3])),
        )

    def inv(A):  # det 1
        return (A[3], F.neg(A[1]), F.neg(A[2]), A[0])

    I = (O, Z, Z, O)
    mI = (F.neg(O), Z, Z, F.neg(O))
    return mm, inv, I, mI


def sl2(F):
    mm, inv, I, mI = make(F)
    out = []
    for a, b, c, d in itertools.product(F.els, repeat=4):
        det = F.add(F.mul(a, d), F.neg(F.mul(b, c)))
        if det == (1, 0):
            out.append((a, b, c, d))
    return out


def power(mm, A, k, I):
    R = I
    for _ in range(k):
        R = mm(R, A)
    return R


def run(F, label):
    mm, inv, I, mI = make(F)
    G = sl2(F)
    A8 = [g for g in G if power(mm, g, 4, I) == mI]
    B3 = [g for g in G if g != I and power(mm, g, 3, I) == I]
    # conjugacy class representatives of A8
    reps, seen = [], set()
    for a in A8:
        if a in seen:
            continue
        reps.append(a)
        for g in G:
            seen.add(mm(mm(g, a), inv(g)))
    tally = {}
    examples = {}
    for a in reps:
        J = mm(a, a)
        Ji = inv(J)
        for b in B3:
            ba = mm(b, a)
            if power(mm, ba, 5, I) != I:
                continue
            X = mm(mm(b, a), b)
            Y1 = mm(mm(J, X), Ji)
            r1 = mm(mm(X, Y1), mm(inv(X), inv(Y1)))
            W = mm(mm(J, mm(b, b)), J)
            Y2 = mm(mm(W, X), inv(W))
            r2 = mm(mm(X, Y2), mm(inv(X), inv(Y2)))
            cl = lambda r: "I" if r == I else ("-I" if r == mI else "other")
            key = f"r1={cl(r1)},r2={cl(r2)}"
            tally[key] = tally.get(key, 0) + 1
            examples.setdefault(key, {"a": a, "b": b})
    return {"q": label, "order_SL2": len(G), "a_classes": len(reps), "tally": tally, "examples": examples}


def main():
    fields = [(Fq(3, 2), "9"), (Fq(5, 2), "25"), (Fq(7, 6), "49")]
    for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]:
        fields.append((Fq(p), str(p)))
    only = sys.argv[1:] if len(sys.argv) > 1 else None
    res = []
    for F, lab in fields:
        if only and lab not in only:
            continue
        r = run(F, lab)
        print(json.dumps({k: r[k] for k in ("q", "order_SL2", "a_classes", "tally")}), flush=True)
        res.append(r)
    json.dump(res, open("out_sl2_twisted.json", "w"), indent=1)


if __name__ == "__main__":
    main()
