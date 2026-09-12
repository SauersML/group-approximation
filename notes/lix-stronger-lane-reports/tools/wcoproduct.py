#!/usr/bin/env python3
"""sp-design for sp-steenrod: the Cartan coefficient C at the top splitting.

W is the standard periodic resolution of F_p over Lambda = F_p[Z/p] = F_p[T]/(T^p - 1):
    W_i = Lambda . e_i ,   d e_{2k+1} = s e_{2k} (s = T - 1),  d e_{2k+2} = N e_{2k+1}.

psi : W -> W (x) W is Lambda-linear for the DIAGONAL action, a chain map, and counital.
Writing psi(e_n) = sum_{a+b=n} sum_{i,j} c^{(n)}_{a,b;i,j} T^i e_a (x) T^j e_b, the
"reduced" coefficient that the Cartan evaluation sees is

    cbar^{(n)}_{a,b} = sum_{i,j} c^{(n)}_{a,b;i,j}      (the functional is T-invariant),

and the constant sp-steenrod needs is

    C := cbar^{(2(p-1))}_{p-1, p-1} ,

because for two degree-1 classes u, v the Cartan formula at index 2(p-1) has exactly ONE
surviving term: D_a(u) = 0 unless 0 <= a <= 1*(p-1), so a + b = 2(p-1) forces a = b = p-1.
Hence c_2 = C * c_1^2 and only C != 0 is needed.

SOLVING FOR psi WITHOUT LINEAR ALGEBRA.  Lambda has an explicit F_p-linear contraction of
W:  h_E(T^j) = 1 + T + ... + T^{j-1} (h_E(1) = 0) on even degrees, h_O(T^j) = [j = p-1] on
odd degrees; then d h + h d = 1 (and = 1 - eta eps in degree 0), checked below.  For the
tensor square, H := h (x) 1 satisfies D H + H D = 1 - (eta eps) (x) 1, so
psi(e_n) = H(alpha_n . psi(e_{n-1})) up to one explicit correction supported in the
a = 0 blocks.  Every step is O(size); p = 13 is instant.
"""
import sys


def zeros(p):
    return [[0] * p for _ in range(p)]


def addm(A, B, p, s=1):
    return [[(A[i][j] + s * B[i][j]) % p for j in range(p)] for i in range(p)]


def shift(M, di, dj, p):
    out = zeros(p)
    for i in range(p):
        for j in range(p):
            if M[i][j] % p:
                out[(i + di) % p][(j + dj) % p] = (out[(i + di) % p][(j + dj) % p]
                                                  + M[i][j]) % p
    return out


def lam_s(p):
    v = [0] * p
    v[1] = 1
    v[0] = (v[0] - 1) % p
    return v


def lam_N(p):
    return [1] * p


def alpha(a, p):
    """d on W_a is multiplication by alpha(a)."""
    return lam_s(p) if a % 2 == 1 else lam_N(p)


def diag_act(lam, M, p):
    out = zeros(p)
    for k in range(p):
        if lam[k] % p:
            out = addm(out, shift(M, k, k, p), p, lam[k])
    return out


def conv_rows(lam, M, p):
    """multiply the FIRST tensor slot by lam."""
    out = zeros(p)
    for k in range(p):
        if lam[k] % p:
            out = addm(out, shift(M, k, 0, p), p, lam[k])
    return out


def conv_cols(lam, M, p):
    out = zeros(p)
    for k in range(p):
        if lam[k] % p:
            out = addm(out, shift(M, 0, k, p), p, lam[k])
    return out


def hmap(a, p):
    """the contraction h_a : W_a -> W_{a+1}, as a p x p matrix acting on the basis T^j."""
    M = zeros(p)
    if a % 2 == 0:                       # h_E(T^j) = 1 + T + ... + T^{j-1}
        for j in range(p):
            for l in range(j):
                M[l][j] = 1
    else:                                # h_O(T^j) = [j = p-1]
        M[0][p - 1] = 1
    return M


def apply_h_rows(a, Mat, p):
    """apply h_a to the FIRST tensor slot of the block matrix Mat."""
    H = hmap(a, p)
    out = zeros(p)
    for i in range(p):
        for j in range(p):
            if Mat[i][j] % p:
                for l in range(p):
                    if H[l][i] % p:
                        out[l][j] = (out[l][j] + H[l][i] * Mat[i][j]) % p
    return out


def apply_h_vec(a, v, p):
    H = hmap(a, p)
    return [sum(H[l][i] * v[i] for i in range(p)) % p for l in range(p)]


def Dop(blocks, n, p):
    """D on degree n -> degree n-1; blocks: dict (a,b) -> matrix."""
    out = {}
    for (a, b), M in blocks.items():
        if a >= 1:
            key = (a - 1, b)
            out[key] = addm(out.get(key, zeros(p)), conv_rows(alpha(a, p), M, p), p)
        if b >= 1:
            key = (a, b - 1)
            sgn = 1 if a % 2 == 0 else -1
            out[key] = addm(out.get(key, zeros(p)), conv_cols(alpha(b, p), M, p), p, sgn)
    return {k: v for k, v in out.items() if any(any(r) for r in v)}


def eq(A, B, p):
    for k in set(list(A) + list(B)):
        MA = A.get(k, zeros(p))
        MB = B.get(k, zeros(p))
        for i in range(p):
            for j in range(p):
                if (MA[i][j] - MB[i][j]) % p:
                    return False
    return True


def check_contraction(p):
    """d h + h d = 1 in positive degrees, = 1 - eta eps in degree 0."""
    bad = []
    for a in range(0, 6):
        for j in range(p):
            v = [0] * p
            v[j] = 1
            t1 = [0] * p
            hv = apply_h_vec(a, v, p)
            lam = alpha(a + 1, p)
            for k in range(p):
                if lam[k] % p:
                    for l in range(p):
                        t1[(l + k) % p] = (t1[(l + k) % p] + lam[k] * hv[l]) % p
            t2 = [0] * p
            if a >= 1:
                dv = [0] * p
                lam = alpha(a, p)
                for k in range(p):
                    if lam[k] % p:
                        for l in range(p):
                            dv[(l + k) % p] = (dv[(l + k) % p] + lam[k] * v[l]) % p
                t2 = apply_h_vec(a - 1, dv, p)
            tot = [(t1[l] + t2[l]) % p for l in range(p)]
            want = v[:]
            if a == 0:
                want = [(v[l] - (1 if l == 0 else 0)) % p for l in range(p)]
            if tot != want:
                bad.append((a, j, tot, want))
    return bad


def build_psi(p, nmax, verbose=False):
    psi = {0: {(0, 0): (lambda M: M)(  # psi(e_0) = e_0 (x) e_0
        [[1 if (i, j) == (0, 0) else 0 for j in range(p)] for i in range(p)])}}
    for n in range(1, nmax + 1):
        Y = {}
        lam = alpha(n, p)
        for (a, b), M in psi[n - 1].items():
            Y[(a, b)] = diag_act(lam, M, p)
        Y = {k: v for k, v in Y.items() if any(any(r) for r in v)}
        assert not Dop(Y, n - 1, p), f"Y is not a cycle at n={n}"
        X = {}
        for (a, b), M in Y.items():
            key = (a + 1, b)
            X[key] = addm(X.get(key, zeros(p)), apply_h_rows(a, M, p), p)
        resid = Dop(X, n, p)
        E = {}
        for k in set(list(Y) + list(resid)):
            M = addm(Y.get(k, zeros(p)), resid.get(k, zeros(p)), p, -1)
            if any(any(r) for r in M):
                E[k] = M
        if E:
            # E is supported in the a = 0 blocks with only the i = 0 row: correct it
            for (a, b), M in list(E.items()):
                assert a == 0, ("unexpected residual block", n, a, b)
                assert all(M[i][j] % p == 0 for i in range(1, p) for j in range(p)), \
                    ("residual is not in the i = 0 row", n, a, b)
                y = [M[0][j] % p for j in range(p)]
                z = apply_h_vec(b, y, p)
                key = (0, b + 1)
                Z = zeros(p)
                for j in range(p):
                    Z[0][j] = z[j]
                X[key] = addm(X.get(key, zeros(p)), Z, p)
        X = {k: v for k, v in X.items() if any(any(r) for r in v)}
        assert eq(Dop(X, n, p), Y, p), f"chain map identity fails at n={n}"
        psi[n] = X
    return psi


def cbar(psi, n, p):
    out = {}
    for (a, b), M in psi[n].items():
        out[(a, b)] = sum(sum(r) for r in M) % p
    return out


def counit_ok(psi, p):
    M = psi[0][(0, 0)]
    return sum(sum(r) for r in M) % p == 1


if __name__ == "__main__":
    primes = [3, 5, 7, 11, 13]
    if len(sys.argv) > 1:
        primes = [int(a) for a in sys.argv[1:]]
    for p in primes:
        bad = check_contraction(p)
        n = 2 * (p - 1)
        psi = build_psi(p, n)
        cb = cbar(psi, n, p)
        C = cb.get((p - 1, p - 1), 0) % p
        print("=" * 66, flush=True)
        print(f"p = {p}: contraction failures {len(bad)}, counit ok {counit_ok(psi, p)}",
              flush=True)
        print(f"  reduced coefficients cbar^({n})_(a,b), a+b = {n}:", flush=True)
        row = ", ".join(f"({a},{b}):{cb.get((a,b),0) if cb.get((a,b),0) <= p//2 else cb[(a,b)]-p}"
                        for a in range(n + 1) for b in [n - a])
        print("    " + row, flush=True)
        print(f"  C = cbar^({n})_({p-1},{p-1}) = {C}   "
              f"({'NONZERO' if C % p else 'ZERO'} mod {p})", flush=True)
        # the low-degree reduced coefficients, to compare with the classical formula
        for m in range(1, min(6, n + 1)):
            cbm = cbar(psi, m, p)
            print(f"    cbar^({m}): " + ", ".join(
                f"({a},{m-a}):{cbm.get((a,m-a),0)}" for a in range(m + 1)), flush=True)
