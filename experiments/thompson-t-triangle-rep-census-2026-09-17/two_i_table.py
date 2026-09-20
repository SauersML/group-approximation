"""Exact-structure check for the near-central regime: G = Delta / <<[a^2, b]>> = 2I.

Delta = <a, b | a^4, b^3, (ba)^5>, X = bab, J = a^2,
r1 = [X, JXJ], r2 = [X, J b^2 J X J b J].

1. Build rho_2: Delta -> SU(2) with a -> order 4, b -> order 3, ba -> order 5.
   Close the image under multiplication, recording a word in a, b for each element.
   Check: |image| = 120 (so image = 2I, and G -> 2I is onto; |G| <= 120 by the
   central-extension-of-A_5 argument, hence G = 2I and rho_2 is faithful on G).
2. Build candidate irreps of G as Delta-representations:
   Sym^k rho_2 (k = 0..5), rho_2', Sym^2 rho_2', rho_2 (x) rho_2',
   where rho_2' = rho_2 o (outer automorphism), realised by a second generating pair.
   Check via characters over the 120 elements that they are irreducible, pairwise
   inequivalent, and that the squares of their dimensions sum to 120 (so they are all irreps).
3. Evaluate D(pi) = max(||pi(r1) - 1||, ||pi(r2) - 1||) on each, and print the table.
"""
import itertools
import numpy as np

phi = (1 + 5 ** 0.5) / 2


def quat(w, x, y, z):
    return np.array([[w + 1j * x, y + 1j * z], [-y + 1j * z, w - 1j * x]])


# the 120 icosians: 24 Hurwitz units and 96 of the form (0, +-1, +-1/phi, +-phi)/2 even perms
def icosians():
    out = []
    for i in range(4):
        for s in (1, -1):
            v = [0, 0, 0, 0]
            v[i] = s
            out.append(v)
    for s in itertools.product((0.5, -0.5), repeat=4):
        out.append(list(s))
    base = [0, 1, 1 / phi, phi]
    evens = [p for p in itertools.permutations(range(4))
             if sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j]) % 2 == 0]
    for p in evens:
        for sg in itertools.product((1, -1), repeat=3):
            v = [0.0] * 4
            vals = [0, sg[0] * 1, sg[1] / phi, sg[2] * phi]
            for k in range(4):
                v[p[k]] = vals[k] / 2
            out.append(v)
    uniq = []
    for v in out:
        if not any(np.allclose(v, u) for u in uniq):
            uniq.append(v)
    return [quat(*v) for v in uniq]


def order(M):
    P = np.eye(2)
    for k in range(1, 200):
        P = P @ M
        if np.allclose(P, np.eye(2)):
            return k
    return None


def close(a, b):
    """BFS closure; returns list of (matrix, word) with words over 'a','b'."""
    elems = [(np.eye(2, dtype=complex), '')]
    frontier = [elems[0]]
    while frontier:
        nf = []
        for M, w in frontier:
            for g, c in ((a, 'a'), (b, 'b')):
                N = M @ g
                if not any(np.allclose(N, E) for E, _ in elems):
                    elems.append((N, w + c))
                    nf.append((N, w + c))
        frontier = nf
    return elems


def ev(word, A, B):
    M = np.eye(A.shape[0], dtype=complex)
    for c in word:
        M = M @ (A if c == 'a' else B)
    return M


def sym(M, k):
    """Sym^k of a 2x2 matrix: restriction of M^(x)k to the symmetric subspace, orthonormal basis."""
    if k == 0:
        return np.eye(1, dtype=complex)
    T = np.eye(1, dtype=complex)
    for _ in range(k):
        T = np.kron(T, M)
    # orthonormal basis of Sym^k(C^2): normalised symmetrisations of e_0^(k-j) e_1^j
    cols = []
    for j in range(k + 1):
        v = np.zeros(2 ** k)
        for idx in range(2 ** k):
            if bin(idx).count('1') == j:
                v[idx] = 1.0
        cols.append(v / np.linalg.norm(v))
    V = np.array(cols).T
    return V.T @ T @ V


def D(A, B):
    n = A.shape[0]
    J = A @ A
    X = B @ A @ B
    ct = lambda M: M.conj().T
    Y1 = J @ X @ J
    Y2 = J @ B @ B @ J @ X @ J @ B @ J
    r1 = X @ Y1 @ ct(X) @ ct(Y1)
    r2 = X @ Y2 @ ct(X) @ ct(Y2)
    I = np.eye(n)
    return np.linalg.norm(r1 - I, 2), np.linalg.norm(r2 - I, 2)


def main():
    G = icosians()
    assert len(G) == 120
    # pick a of order 4, b of order 3 with ba of order 10 (trace phi, resp. -1/phi)
    fours = [M for M in G if abs(np.trace(M)) < 1e-12]
    threes = [M for M in G if abs(np.trace(M) + 1) < 1e-12]
    pair, pair2 = None, None
    for a in fours:
        for b in threes:
            t = np.trace(b @ a).real
            if pair is None and abs(t - phi) < 1e-12:
                pair = (a, b)
            if pair2 is None and abs(t - (phi - 1) * -1) < 1e-12:  # trace -1/phi: angle 3pi/5
                pair2 = (a, b)
        if pair and pair2:
            break
    # replace a by -a: still order 4 with a^2 = -1, and ba becomes order 5, so (ba)^5 = 1
    # holds exactly and these are honest representations of Delta (Delta is perfect, so every
    # representation lands in SU(n)).  The sign does not change r1, r2 (X appears once per slot).
    a, b = -pair[0], pair[1]
    a2, b2 = -pair2[0], pair2[1]
    assert order(a) == 4 and order(b) == 3 and order(b @ a) == 5
    assert order(a2) == 4 and order(b2) == 3 and order(b2 @ a2) == 5
    els = close(a, b)
    print('|<rho_2(a), rho_2(b)>| =', len(els))
    assert len(els) == 120
    assert len(close(a2, b2)) == 120
    # [a^2, b] = 1 in both
    assert np.allclose(a @ a @ b, b @ a @ a) and np.allclose(a2 @ a2 @ b2, b2 @ a2 @ a2)
    words = [w for _, w in els]
    # check that a -> a2, b -> b2 is a well-defined map on G: equal words in rho_2 give equal in pair2
    # (it suffices that the relations of G hold; we check the multiplication table is respected)
    img2 = [ev(w, a2, b2) for w in words]
    for i, (M, _) in enumerate(els):
        for g, g2 in ((a, a2), (b, b2)):
            N = M @ g
            j = next(k for k, (E, _) in enumerate(els) if np.allclose(N, E))
            assert np.allclose(img2[i] @ g2, img2[j])
    print('a -> a2, b -> b2 extends to a homomorphism G -> 2I (checked on the Cayley graph)')

    reps = {}
    for k in range(6):
        reps['Sym^%d rho_2' % k] = (sym(a, k), sym(b, k))
    reps["rho_2'"] = (a2, b2)
    reps["Sym^2 rho_2'"] = (sym(a2, 2), sym(b2, 2))
    reps["rho_2 (x) rho_2'"] = (np.kron(a, a2), np.kron(b, b2))
    chars = {}
    for name, (A, B) in reps.items():
        n = A.shape[0]
        assert np.allclose(A.conj().T @ A, np.eye(n)) and np.allclose(B.conj().T @ B, np.eye(n))
        assert np.allclose(np.linalg.matrix_power(A, 4), np.eye(n))
        assert np.allclose(np.linalg.matrix_power(B, 3), np.eye(n))
        assert np.allclose(np.linalg.matrix_power(B @ A, 5), np.eye(n))
        assert np.allclose(A @ A @ B, B @ A @ A)
        chars[name] = np.array([np.trace(ev(w, A, B)) for w in words])
    names = list(reps)
    gram = np.array([[np.vdot(chars[p], chars[q]) / 120 for q in names] for p in names])
    assert np.allclose(gram, np.eye(len(names))), gram.round(3)
    dims = [reps[nm][0].shape[0] for nm in names]
    assert sum(d * d for d in dims) == 120
    print('9 candidate reps: orthonormal characters, sum of dim^2 = 120 -> complete list of irreps of G')
    print('%-18s %4s %10s %10s %10s' % ('irrep', 'dim', 'd1', 'd2', 'D'))
    best = None
    for nm in names:
        A, B = reps[nm]
        d1, d2 = D(A, B)
        print('%-18s %4d %10.6f %10.6f %10.6f' % (nm, A.shape[0], d1, d2, max(d1, d2)))
        if A.shape[0] > 1 and (best is None or max(d1, d2) < best[0]):
            best = (max(d1, d2), nm)
    print('min over nontrivial irreps: %.12f at %s ; (sqrt5-1)/2 = %.12f' % (best[0], best[1], (5 ** 0.5 - 1) / 2))


if __name__ == '__main__':
    main()
