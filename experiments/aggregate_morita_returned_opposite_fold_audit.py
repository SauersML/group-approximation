"""Audit the first common-opposite return of the aggregate Morita fold.

Run on MSI only.  The two branches are represented in two copies of
GL_3(F_2).  The common reverse parent root is the diagonal pair of reverse
long roots, so its commutators with the literal s_i/t_i arms recover two
returned payload paths.  Their commutators are the two reverse child roots.
"""


def identity(size):
    return tuple(
        tuple(1 if row == column else 0 for column in range(size))
        for row in range(size)
    )


def multiply(left, right):
    size = len(left)
    return tuple(
        tuple(
            sum(left[row][middle] * right[middle][column]
                for middle in range(size)) % 2
            for column in range(size)
        )
        for row in range(size)
    )


def transvection(row, column):
    answer = [list(entry) for entry in identity(3)]
    answer[row][column] = 1
    return tuple(tuple(entry) for entry in answer)


def pair_multiply(left, right):
    return multiply(left[0], right[0]), multiply(left[1], right[1])


def pair_inverse(element):
    # Gaussian elimination would be overkill for this fixed audit.  Search
    # the at-most-six powers of each component.
    components = []
    for component in element:
        candidate = identity(3)
        for _ in range(1, 8):
            candidate = multiply(candidate, component)
            if multiply(component, candidate) == identity(3):
                components.append(candidate)
                break
        else:
            raise AssertionError("component inverse not found")
    return tuple(components)


def commutator(left, right):
    return pair_multiply(
        pair_multiply(pair_multiply(left, right), pair_inverse(left)),
        pair_inverse(right),
    )


def power(element, exponent):
    answer = (identity(3), identity(3))
    for _ in range(exponent):
        answer = pair_multiply(answer, element)
    return answer


def permutation_multiply(left, right):
    return tuple(left[right[index]] for index in range(len(left)))


def permutation_inverse(element):
    answer = [0] * len(element)
    for source, target in enumerate(element):
        answer[target] = source
    return tuple(answer)


def permutation_commutator(left, right):
    return permutation_multiply(
        permutation_multiply(
            permutation_multiply(left, right), permutation_inverse(left)),
        permutation_inverse(right),
    )


def audit_old_dihedral_factor():
    # In one old D8 branch, S=a and T=b.  A possible component d of the new
    # common reverse root would have to satisfy
    # d=[[d,a],[b,d]].  Exhaust the eight elements: only d=1 works.
    one = tuple(range(4))
    a = (1, 0, 3, 2)
    b = (0, 3, 2, 1)
    group = {one}
    pending = [a, b]
    while pending:
        element = pending.pop()
        if element in group:
            continue
        group.add(element)
        for known in tuple(group):
            pending.append(permutation_multiply(element, known))
            pending.append(permutation_multiply(known, element))
    assert len(group) == 8
    solutions = []
    for d in group:
        u = permutation_commutator(d, a)
        v = permutation_commutator(b, d)
        if permutation_commutator(u, v) == d:
            solutions.append(d)
    assert solutions == [one]


def main():
    audit_old_dihedral_factor()
    one = identity(3)
    trivial = (one, one)

    # In one GL_3(F_2) branch the coordinate order is (7, k_i, 8).
    s = transvection(0, 1)
    t = transvection(1, 2)
    c = transvection(0, 2)
    reverse = transvection(2, 0)
    u = transvection(2, 1)
    v = transvection(1, 0)

    S0, S1 = (s, one), (one, s)
    T0, T1 = (t, one), (one, t)
    C0, C1 = (c, one), (one, c)
    R0, R1 = (reverse, one), (one, reverse)
    U0, U1 = (u, one), (one, u)
    V0, V1 = (v, one), (one, v)

    A = pair_multiply(S0, S1)
    B = pair_multiply(T0, T1)
    N = pair_multiply(C0, C1)
    D = pair_multiply(R0, R1)

    assert commutator(S0, S1) == trivial
    assert commutator(T0, T1) == trivial
    assert commutator(S0, T1) == trivial
    assert commutator(S1, T0) == trivial
    assert commutator(S0, T0) == C0
    assert commutator(S1, T1) == C1
    assert commutator(A, B) == N

    assert commutator(D, S0) == U0
    assert commutator(D, S1) == U1
    assert commutator(T0, D) == V0
    assert commutator(T1, D) == V1
    assert commutator(U0, V0) == R0
    assert commutator(U1, V1) == R1
    assert pair_multiply(R0, R1) == D

    # Different children commute.  Only the full-coefficient aggregate
    # parents need an opposite-root Whitehead relation.
    assert commutator(C0, R1) == trivial
    assert commutator(C1, R0) == trivial
    assert pair_multiply(pair_multiply(N, D), N) == pair_multiply(
        pair_multiply(D, N), D)
    assert power(pair_multiply(N, D), 3) == trivial

    assert C1 != trivial
    assert N != trivial
    print("D8^2 broken; exact GL3(F2)^2 returned-opposite model; marked C1 survives")


if __name__ == "__main__":
    main()
