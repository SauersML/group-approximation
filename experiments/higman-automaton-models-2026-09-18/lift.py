# Level-by-level lifting of actions of a finitely presented group on the binary rooted tree.
#
# A level-L action is given by permutations p_g of the 2^L vertices of level L. A lift to level
# L+1 is g(2v + x) = 2 p_g(v) + (x xor f_g(v)) with decorations f_g in F_2^(2^L). For a word
# w = l_1 ... l_k (acting as l_1 o ... o l_k) the decoration is f_w = sum_i f_{l_i} o p_{l_(i+1)...l_k},
# which is F_2-linear in the unknowns f_g(u). So the lifts satisfying all relators form the kernel
# of an explicit F_2-matrix (Shapiro: it is Z^1 of the group with coefficients in F_2[level L]).
# Every solution gives a finite 2-group quotient (the image at level L+1); a tower of solutions
# gives a homomorphism to Aut(T_2), a pro-2 group.
#
# usage: python3 lift.py <n> <extra> <Lmax> <seed>
#   extra = none | ac2 (add [a,c]^2) ; greedy: at each level pick the solution that maximises
#   the number of doubled a-cycles among a few random kernel vectors.
import sys, random
import numpy as np

GEN = 4
NAMES = "abcd"


def parse(word):
    # word string over a,b,c,d, capitals = inverses
    return [(NAMES.index(ch.lower()), 1 if ch.islower() else -1) for ch in word]


def relators(n, extra):
    rs = []
    for g in range(GEN):
        y, x = NAMES[g], NAMES[(g + 1) % GEN]  # y^-1 x y x^-n
        rs.append(parse(y.upper() + x + y + x.upper() * n))
    if extra == "ac2":
        rs.append(parse("ACac" * 2))
    return rs


def inv(p):
    q = np.empty_like(p)
    q[p] = np.arange(len(p))
    return q


def word_decoration_terms(P, Pinv, w, size):
    """Return list of (gen, index_array) with f_w(v) = sum_t f_gen(index_array[v]) mod 2."""
    terms = []
    suffix = np.arange(size)  # p_{l_(i+1)..l_k}(v)
    for g, e in reversed(w):
        if e == 1:
            terms.append((g, suffix.copy()))
            suffix = P[g][suffix]
        else:
            # f_{g^-1}(u) = f_g(p_g^-1(u))
            suffix = Pinv[g][suffix]
            terms.append((g, suffix.copy()))
    return terms, suffix


def build_rows(P, Pinv, rels, size):
    rows = []
    for r in rels:
        terms, _ = word_decoration_terms(P, Pinv, r, size)
        for v in range(size):
            row = 0
            for g, idx in terms:
                row ^= 1 << (g * size + int(idx[v]))
            if row:
                rows.append(row)
    return rows


def nullspace(rows, ncols):
    # Gaussian elimination over F_2 with Python ints; returns a basis of the kernel.
    pivots = {}  # pivot col -> row
    for r in rows:
        while r:
            c = r.bit_length() - 1
            if c in pivots:
                r ^= pivots[c]
            else:
                pivots[c] = r
                break
    # reduce to RREF
    cols = sorted(pivots)
    for c in cols:
        rc = pivots[c]
        for c2 in cols:
            if c2 > c and (pivots[c2] >> c) & 1:
                pivots[c2] ^= rc
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fcol in free:
        vec = 1 << fcol
        for c, rc in pivots.items():
            if (rc >> fcol) & 1:
                vec |= 1 << c
        basis.append(vec)
    return basis


def cycles(p):
    n = len(p)
    seen = np.zeros(n, dtype=bool)
    out = []
    for i in range(n):
        if not seen[i]:
            cyc = []
            j = i
            while not seen[j]:
                seen[j] = True
                cyc.append(j)
                j = p[j]
            out.append(cyc)
    return out


def apply_lift(P, vec, size):
    newP = []
    for g in range(GEN):
        f = np.array([(vec >> (g * size + v)) & 1 for v in range(size)], dtype=np.int64)
        arr = np.empty(2 * size, dtype=np.int64)
        v = np.arange(size)
        for x in (0, 1):
            arr[2 * v + x] = 2 * P[g][v] + (x ^ f)
        newP.append(arr)
    return newP


def score(vec, cyc_a, size, g=0):
    s = 0
    for cyc in cyc_a:
        t = 0
        for v in cyc:
            t ^= (vec >> (g * size + int(v))) & 1
        s += t * len(cyc)
    return s


def main():
    n = int(sys.argv[1]); extra = sys.argv[2]; Lmax = int(sys.argv[3]); seed = int(sys.argv[4])
    tries = int(sys.argv[5]) if len(sys.argv) > 5 else 8
    rnd = random.Random(seed)
    rels = relators(n, extra)
    P = [np.zeros(1, dtype=np.int64) for _ in range(GEN)]
    from math import lcm, log2
    for L in range(0, Lmax):
        size = 1 << L
        Pinv = [inv(p) for p in P]
        rows = build_rows(P, Pinv, rels, size)
        basis = nullspace(rows, GEN * size)
        cyc_a = cycles(P[0])
        best, bs = 0, -1
        for _ in range(tries):
            vec = 0
            for bvec in basis:
                if rnd.random() < 0.5:
                    vec ^= bvec
            s = score(vec, cyc_a, size)
            if s > bs:
                best, bs = vec, s
        P = apply_lift(P, best, size)
        ords = []
        for g in range(GEN):
            o = 1
            for cyc in cycles(P[g]):
                o = lcm(o, len(cyc))
            ords.append(int(log2(o)))
        print("level %d: kernel dim %d (unknowns %d), log2 orders %s" % (L + 1, len(basis), GEN * size, ords), flush=True)
    np.save("lift_%d_%s_%d.npy" % (n, extra, seed), np.array(P))


if __name__ == "__main__":
    main()
