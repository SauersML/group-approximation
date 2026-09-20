"""Census of the transverse cohomology H^1(Z/4*Z/3; p) for classical embeddings.

For Gamma = Z/4 * Z/3 acting on a finite-dimensional module W through a pair (A, B),
Mayer--Vietoris on the Bass--Serre tree gives

    dim H^0(Gamma; W) - dim H^1(Gamma; W) = dim W^A + dim W^B - dim W.

Here W is p, the orthogonal complement of the subalgebra k in su(n), where
    k = so(n) inside su(n)      (p = Sym^2_0 C^n),  or
    k = sp(m) inside su(2m)     (p = Lambda^2_0 C^(2m)).
When <A, B> is dense in the subgroup, W^Gamma = 0, so
    H^1(Gamma; p) = dim p - dim p^A - dim p^B.

The script lists every eigenvalue-multiplicity pattern of A (A^4 central) and B (B^3 central)
that passes the necessary conditions for density:
  * no common eigenvector on C^n, i.e. m_lambda(A) + m_mu(B) <= n for all lambda, mu;
  * H^1(Gamma; k) >= 0, i.e. k^A + k^B <= dim k.
(H^1(Gamma; p) < 0 is also excluded by density, since it forces p^A and p^B to meet.)
For each such pattern it reports whether H^1(Gamma; p) = 0.

Output: the patterns with H^1(Gamma; p) = 0, called transversally rigid. For these, the
genericity argument cannot push the pair off the subgroup.
"""
import sys
from fractions import Fraction


def so_classes_A(k):
    out = []
    # A^4 = 1 : eigenvalues 1 (a), -1 (b), +-i (c pairs); det = (-1)^b = 1
    for c in range(0, k // 2 + 1):
        for a in range(0, k - 2 * c + 1):
            b = k - 2 * c - a
            if b % 2:
                continue
            mult = [a, b, c, c]
            sym = a * (a + 1) // 2 + b * (b + 1) // 2 + c * c
            alt = a * (a - 1) // 2 + b * (b - 1) // 2 + c * c
            out.append((("A^4=1", a, b, c), mult, sym, alt))
    if k % 2 == 0:
        # A^4 = -1 : eigenvalues e^{+-i pi/4} (c1 pairs), e^{+-3 i pi/4} (c2 pairs)
        for c1 in range(0, k // 2 + 1):
            c2 = k // 2 - c1
            f = c1 * c1 + c2 * c2
            out.append((("A^4=-1", c1, c2), [c1, c1, c2, c2], f, f))
    return out


def so_classes_B(k):
    out = []
    # B^3 = 1 (B^3 = -1 reduces to this by B -> -B, since -1 in SO(k) for k even)
    for e in range(0, k // 2 + 1):
        d = k - 2 * e
        out.append((("B^3=1", d, e), [d, e, e], d * (d + 1) // 2 + e * e, d * (d - 1) // 2 + e * e))
    return out


def so_census(kmax):
    bad = []
    for k in range(3, kmax + 1):
        if k == 4:
            continue
        dp = k * (k + 1) // 2 - 1
        dm = k * (k - 1) // 2
        for (na, ma, sa, la) in so_classes_A(k):
            for (nb, mb, sb, lb) in so_classes_B(k):
                h1m = dm - la - lb
                if h1m < 0:
                    continue
                if max(ma) + max(mb) > k:
                    continue
                h1p = dp - (sa - 1) - (sb - 1)
                if h1p == 0:
                    bad.append((k, na, nb, h1p, h1m))
    return bad


def sp_classes_A(m):
    # Sp(m) in SU(2m); eigenvalues of A come in pairs lambda, lambda^{-1}.
    # A^4 = 1: +1 (2a), -1 (2b), +-i (c each); a+b+c = m  (multiplicities of +-1 are even)
    out = []
    for c in range(0, m + 1):
        for a in range(0, m - c + 1):
            b = m - c - a
            A1, Am, Ai = 2 * a, 2 * b, c
            # Lambda^2 fixed: pairs with product 1
            alt = A1 * (A1 - 1) // 2 + Am * (Am - 1) // 2 + Ai * Ai
            sym = A1 * (A1 + 1) // 2 + Am * (Am + 1) // 2 + Ai * Ai
            out.append((("A^4=1", A1, Am, Ai), [A1, Am, Ai, Ai], sym, alt))
    # A^4 = -1: e^{+-i pi/4} (c1 each), e^{+-3i pi/4} (c2 each), c1 + c2 = m
    for c1 in range(0, m + 1):
        c2 = m - c1
        f = c1 * c1 + c2 * c2
        out.append((("A^4=-1", c1, c2), [c1, c1, c2, c2], f, f))
    return out


def sp_classes_B(m):
    out = []
    # B^3 = 1: 1 (2d... not forced even? eigenvalue 1 has even multiplicity in Sp) ; omega, omegabar (e each)
    for e in range(0, m + 1):
        d = 2 * (m - e)
        out.append((("B^3=1", d, e), [d, e, e], d * (d + 1) // 2 + e * e, d * (d - 1) // 2 + e * e))
    return out


def sp_census(mmax):
    bad = []
    for m in range(2, mmax + 1):
        n = 2 * m
        dk = m * (2 * m + 1)          # sp(m) = Sym^2 C^(2m)
        dp = m * (2 * m - 1) - 1      # Lambda^2_0 C^(2m)
        for (na, ma, sa, la) in sp_classes_A(m):
            for (nb, mb, sb, lb) in sp_classes_B(m):
                h1k = dk - sa - sb
                if h1k < 0:
                    continue
                if max(ma) + max(mb) > n:
                    continue
                h1p = dp - (la - 1) - (lb - 1)
                if h1p == 0:
                    bad.append((m, na, nb, h1p, h1k))
    return bad


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    so = so_census(kmax)
    sp = sp_census(kmax // 2)
    print("SO(k), 3<=k<=%d, k!=4: patterns with H^1(p)=0 passing the necessary density tests: %d" % (kmax, len(so)))
    for row in so:
        print("  SO", row)
    print("Sp(m), 2<=m<=%d: patterns with H^1(p)=0 passing the necessary density tests: %d" % (kmax // 2, len(sp)))
    for row in sp:
        print("  Sp", row)
