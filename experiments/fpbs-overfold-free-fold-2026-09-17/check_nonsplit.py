"""Independent check (Reidemeister-Schreier) of the non-split example found
by retract_test.py at j = 1, d = 3.

Q = Z/3 with a = +1, b = -1; S = Stab_L(0); K' = S cap L_1 (L_1 = <a, t>,
t = b a b^-2, acting as -1).  The two-seed witness there is J = S (the
closure collapses Gamma_2(Q) onto Q), and law(K') = 2.
Computes the matrix of H_1(K') -> H_1(S) in Schreier bases and its
determinant.  |det| != 1 means H_1(K') -> H_1(S) is not split, so K' is not
a retract (nor a free factor) of the minimum witness S.
"""
from sympy import Matrix

N = 3
ACT = {'a': 1, 'b': -1, 'A': -1, 'B': 1}  # A = a^-1, B = b^-1


def schreier_gens_S():
    """Transversal a^i (i = 0,1,2); generators (i, x) for x in {a, b} with
    rep(i) x rep(i x)^-1 nontrivial (i.e. excluding tree edges a: i -> i+1
    for i = 0, 1)."""
    gens = {}
    for i in range(N):
        for x in 'ab':
            if x == 'a' and i < N - 1:
                continue  # tree edge
            gens[(i, x)] = len(gens)
    return gens


def h1_S(word, gens):
    """Class in H_1(S) = Z^4 of a closed word (starting at 0)."""
    vec = [0] * len(gens)
    p = 0
    for x in word:
        if x in 'ab':
            if (p, x) in gens:
                vec[gens[(p, x)]] += 1
            p = (p + ACT[x]) % N
        else:
            q = (p + ACT[x]) % N  # edge q --x.lower()--> p traversed back
            if (q, x.lower()) in gens:
                vec[gens[(q, x.lower())]] -= 1
            p = q
    assert p == 0, word
    return vec


def main():
    gens = schreier_gens_S()
    T = 'baBB'
    # L_1-set: a = +1, t = -1 on Z/3; Schreier generators of Stab(0) in L_1
    # with transversal a^i: (i, a) for i = 2 and (i, t) for all i.
    kgens = []
    for i in range(N):
        rep = 'a' * i
        for x, w, dx in (('a', 'a', 1), ('t', T, -1)):
            if x == 'a' and i < N - 1:
                continue
            j = (i + dx) % N
            back = 'A' * j
            kgens.append(rep + w + back)
    assert len(kgens) == 4
    M = Matrix([h1_S(w, gens) for w in kgens]).T
    print('H_1(K\') -> H_1(S) matrix (columns = K\' generators):')
    print(M)
    print('det =', M.det())


if __name__ == '__main__':
    main()
