"""Audit the literal inverse-pair letters against the row-one native actor.

Run on MSI only.  The calculation stays inside the fixed words

    u=x_75(t0), v=x_56(s0), T=J1 B2 A1, a=x_97(1),

and records the exact actor orbit before the coefficient product in [u,v]
collapses to one.  Coefficients use the faithful binary-prefix normal form.
"""

from depth_one_paired_leavitt_return_search import (
    COORDS, ONE, ZERO, add, canonical, equal, identity_matrix,
    left_elementary, multiply,
)
from support_partial_whitehead_native_return_audit import (
    matrices_equal, matrix_multiply,
)
from depth_one_paired_leavitt_return_search import signed_l0
from individual_cross_whitehead_one_return_search import full_signed_signature


def coeff(mu, nu):
    return canonical(((mu, nu),))


def root(row, column, coefficient):
    return (column, row, coefficient)


def word_matrix(factors):
    matrix = identity_matrix()
    for factor in reversed(factors):
        matrix = left_elementary(matrix, *factor)
    return matrix


def power(matrix, exponent):
    answer = identity_matrix()
    for _ in range(exponent):
        answer = matrix_multiply(answer, matrix)
    return answer


def conjugate(actor, actor_inverse, matrix):
    return matrix_multiply(matrix_multiply(actor, matrix), actor_inverse)


def commutator(left, left_inverse, right, right_inverse):
    return matrix_multiply(
        matrix_multiply(matrix_multiply(left, right), left_inverse),
        right_inverse,
    )


def nonidentity_entries(matrix):
    entries = []
    for row, row_coordinate in enumerate(COORDS):
        for column, column_coordinate in enumerate(COORDS):
            expected = ONE if row == column else ZERO
            if not equal(matrix[row][column], expected):
                entries.append((row_coordinate, column_coordinate,
                                matrix[row][column]))
    return entries


def monomial_identity(size):
    return tuple(range(size)), (1,) * size


def monomial_multiply(left, right):
    left_image, left_sign = left
    right_image, right_sign = right
    return (
        tuple(left_image[right_image[index]] for index in range(len(left_image))),
        tuple(right_sign[index] * left_sign[right_image[index]]
              for index in range(len(left_image))),
    )


def monomial_inverse(operator):
    image, sign = operator
    inverse_image = [0] * len(image)
    inverse_sign = [0] * len(image)
    for source, target in enumerate(image):
        inverse_image[target] = source
        inverse_sign[target] = sign[source]
    return tuple(inverse_image), tuple(inverse_sign)


def monomial_power(operator, exponent):
    answer = monomial_identity(len(operator[0]))
    for _ in range(exponent):
        answer = monomial_multiply(answer, operator)
    return answer


def monomial_commutator(left, right):
    return monomial_multiply(
        monomial_multiply(
            monomial_multiply(left, right), monomial_inverse(left)),
        monomial_inverse(right),
    )


def gauge_model():
    # Coordinates are (seven-cycle stage, native gauge bit, nested chart,
    # returned-gauge block bit, Pauli auxiliary bit).  Every operator below is
    # a signed permutation, so this is an exact finite unitary model.
    coordinates = tuple(
        (stage, d_bit, chart, e_bit, aux)
        for stage in range(7)
        for d_bit in range(2)
        for chart in range(2)
        for e_bit in range(2)
        for aux in range(2)
    )
    position = {coordinate: index for index, coordinate in enumerate(coordinates)}

    def operator(action):
        images = []
        signs = []
        for coordinate in coordinates:
            target, sign = action(*coordinate)
            images.append(position[target])
            signs.append(sign)
        return tuple(images), tuple(signs)

    identity = monomial_identity(len(coordinates))
    D = operator(lambda k, d, c, e, x: ((k, d, c, e, x), -1 if d else 1))
    E = operator(lambda k, d, c, e, x: ((k, d, c, e, x), -1 if e else 1))

    # A seven-cycle whose first two edges carry D has trivial cyclic holonomy.
    T = operator(lambda k, d, c, e, x: (
        ((k + 1) % 7, d, c, e, x),
        -1 if k in (0, 1) and d else 1,
    ))
    # A local Whitehead chart swap carrying the same native gauge D.
    J = operator(lambda k, d, c, e, x: (
        ((1 if k == 0 else 0 if k == 1 else k), d, c, e, x),
        -1 if k in (0, 1) and d else 1,
    ))
    K = operator(lambda k, d, c, e, x: (
        ((k, d, c, e, x), -1 if k == 0 else 1)
    ))
    U0 = operator(lambda k, d, c, e, x: (
        (k, d, c, e, 1 - x if c and e else x), 1
    ))
    V = operator(lambda k, d, c, e, x: (
        (k, d, c, e, x), -1 if c and e and x else 1
    ))
    U = monomial_multiply(K, U0)
    A = operator(lambda k, d, c, e, x: ((k, d, 1 - c, e, x), 1))

    H = monomial_commutator(U, V)
    N = monomial_commutator(A, H)
    R = monomial_power(monomial_multiply(T, U), 7)
    G = monomial_commutator(R, V)
    M = monomial_commutator(A, G)

    assert monomial_power(T, 7) == identity
    assert monomial_power(J, 2) == identity
    assert monomial_power(U, 2) == identity
    assert monomial_power(V, 2) == identity
    assert monomial_power(A, 2) == identity
    assert monomial_commutator(T, V) == identity
    assert monomial_commutator(T, N) == identity
    assert monomial_commutator(J, V) == identity
    assert monomial_commutator(J, N) == identity
    assert N == E
    assert M == N
    assert D != E
    assert monomial_multiply(D, E) != identity
    print("112-dimensional moving-chart model: native D and returned E independent")


def orbit_gauge_model():
    # The stronger minimal menu uses two involutions P,Q whose T-orbit norms
    # are one and whose commutator is the returned gauge.  A three-qubit
    # Singer/Pauli model realizes those relations while a separate moving
    # seven-chart factor retains an independent native transition gauge.
    coordinates = tuple(
        (stage, d_bit, label, e_bit)
        for stage in range(7)
        for d_bit in range(2)
        for label in range(8)
        for e_bit in range(2)
    )
    position = {coordinate: index for index, coordinate in enumerate(coordinates)}

    def operator(action):
        images = []
        signs = []
        for coordinate in coordinates:
            target, sign = action(*coordinate)
            images.append(position[target])
            signs.append(sign)
        return tuple(images), tuple(signs)

    def singer_once(label):
        bits = ((label >> 0) & 1, (label >> 1) & 1, (label >> 2) & 1)
        image = (
            bits[0] ^ bits[1],
            bits[0] ^ bits[1] ^ bits[2],
            bits[1],
        )
        return image[0] | (image[1] << 1) | (image[2] << 2)

    def singer(label):
        # The third power gives the stage numbering of the literal orbit table.
        for _ in range(3):
            label = singer_once(label)
        return label

    identity = monomial_identity(len(coordinates))
    D = operator(lambda k, d, label, e: (
        (k, d, label, e), -1 if d else 1
    ))
    E = operator(lambda k, d, label, e: (
        (k, d, label, e), -1 if e else 1
    ))
    T = operator(lambda k, d, label, e: (
        ((k + 1) % 7, d, singer(label), e),
        -1 if k in (0, 1) and d else 1,
    ))
    singer_inverse = {singer(label): label for label in range(8)}
    expected_first_row = (1, 1, 1, 0, 0, 1, 0)
    pauli_pair = None
    for x_mask in range(1, 8):
        for z_mask in range(1, 8):
            moving = x_mask
            row = []
            for _ in range(7):
                row.append((moving & z_mask).bit_count() & 1)
                moving = singer_inverse[moving]
            if tuple(row) == expected_first_row:
                pauli_pair = (x_mask, z_mask)
                break
        if pauli_pair is not None:
            break
    assert pauli_pair is not None
    x_mask, z_mask = pauli_pair
    P = operator(lambda k, d, label, e: (
        (k, d, label ^ x_mask if e else label, e), 1
    ))
    Q = operator(lambda k, d, label, e: (
        (k, d, label, e),
        -1 if e and ((label & z_mask).bit_count() & 1) else 1,
    ))

    def orbit_product(actor, occurrence, reverse=False):
        answer = identity
        powers = range(6, -1, -1) if reverse else range(7)
        actor_inverse = monomial_inverse(actor)
        for exponent in powers:
            conjugate_occurrence = monomial_multiply(
                monomial_multiply(monomial_power(actor, exponent), occurrence),
                monomial_power(actor_inverse, exponent),
            )
            answer = monomial_multiply(answer, conjugate_occurrence)
        return answer

    assert monomial_power(T, 7) == identity
    assert monomial_power(P, 2) == identity
    assert monomial_power(Q, 2) == identity
    assert orbit_product(T, P) == identity
    assert orbit_product(T, P, reverse=True) == identity
    assert orbit_product(T, Q) == identity
    assert orbit_product(T, Q, reverse=True) == identity
    assert monomial_commutator(P, Q) == E
    assert monomial_commutator(T, E) == identity
    model_table = []
    T_inverse = monomial_inverse(T)
    for k in range(7):
        Pk = monomial_multiply(
            monomial_multiply(monomial_power(T, k), P),
            monomial_power(T_inverse, k),
        )
        row = []
        for l in range(7):
            Ql = monomial_multiply(
                monomial_multiply(monomial_power(T, l), Q),
                monomial_power(T_inverse, l),
            )
            cross = monomial_commutator(Pk, Ql)
            if cross == identity:
                row.append(0)
            elif cross == E:
                row.append(1)
            else:
                raise AssertionError("noncentral model cross commutator")
        model_table.append(tuple(row))
    expected_table = (
        (1, 1, 1, 0, 0, 1, 0),
        (0, 1, 1, 1, 0, 0, 1),
        (1, 0, 1, 1, 1, 0, 0),
        (0, 1, 0, 1, 1, 1, 0),
        (0, 0, 1, 0, 1, 1, 1),
        (1, 0, 0, 1, 0, 1, 1),
        (1, 1, 0, 0, 1, 0, 1),
    )
    assert tuple(model_table) == expected_table
    assert D != E
    assert monomial_multiply(D, E) != identity
    print("224-dimensional odd-orbit model: both norms close, D and E remain independent")


def main():
    one = ONE
    t0 = coeff("", "0")
    s0 = coeff("0", "")

    a1 = coeff("1", "0")
    b2 = coeff("00", "1")
    x1 = coeff("00", "0")
    y1 = coeff("0", "00")

    A1 = (root(4, 7, a1),)
    B2 = (root(8, 4, b2),)
    J1 = (
        root(8, 7, x1),
        root(7, 8, y1),
        root(8, 7, x1),
    )
    T_word = J1 + B2 + A1
    T_inverse_word = tuple(reversed(T_word))

    u_word = (root(7, 5, t0),)
    v_word = (root(5, 6, s0),)
    a_word = (root(9, 7, one),)
    h_word = (root(7, 6, one),)
    n_word = (root(9, 6, one),)
    p_word = (root(9, 7, t0),)
    q_word = (root(7, 6, s0),)

    T = word_matrix(T_word)
    T_inverse = word_matrix(T_inverse_word)
    J = word_matrix(J1)
    u = word_matrix(u_word)
    v = word_matrix(v_word)
    a = word_matrix(a_word)
    h = word_matrix(h_word)
    n = word_matrix(n_word)
    p = word_matrix(p_word)
    q = word_matrix(q_word)

    identity = identity_matrix()
    assert matrices_equal(matrix_multiply(T, T_inverse), identity)
    assert matrices_equal(power(J, 2), identity)
    assert matrices_equal(power(T, 7), identity)
    assert matrices_equal(commutator(u, u, v, v), h)
    assert matrices_equal(commutator(a, a, h, h), n)
    assert matrices_equal(commutator(p, p, q, q), n)

    assert matrices_equal(conjugate(T, T_inverse, v), v)
    assert matrices_equal(conjugate(T, T_inverse, n), n)
    assert matrices_equal(conjugate(J, J, v), v)
    assert matrices_equal(conjugate(J, J, n), n)
    character = signed_l0()
    assert full_signed_signature(n_word, character) is not None

    orbit = []
    actor = identity
    actor_inverse = identity
    for _ in range(7):
        orbit.append(conjugate(actor, actor_inverse, u))
        actor = matrix_multiply(T, actor)
        actor_inverse = matrix_multiply(actor_inverse, T_inverse)
    orbit_product = identity
    for occurrence in orbit:
        orbit_product = matrix_multiply(orbit_product, occurrence)

    Tu = matrix_multiply(T, u)
    print("T^7=1")
    print("J^2=1; [J,v]=1 and [J,n]=1")
    print("[T,v]=1 and [T,n]=1")
    print("(T u)^7 identity", matrices_equal(power(Tu, 7), identity))
    print("ordered u-orbit product identity",
          matrices_equal(orbit_product, identity))
    print("(T u)^7 entries", nonidentity_entries(power(Tu, 7)))
    print("ordered orbit-product entries", nonidentity_entries(orbit_product))
    print("u orbit widths", [len(nonidentity_entries(item)) for item in orbit])
    print("J u J entries", nonidentity_entries(conjugate(J, J, u)))
    print("(J u)^2 entries", nonidentity_entries(power(matrix_multiply(J, u), 2)))

    for step in range(1, 7):
        stepped_actor = power(T, step)
        residual = power(matrix_multiply(stepped_actor, u), 7)
        residual_v = commutator(residual, residual, v, v)
        residual_v_a = commutator(a, a, residual_v, residual_v)
        print(f"(T^{step} u)^7 entries", nonidentity_entries(residual))
        print(f"[a,[(T^{step} u)^7,v]] entries",
              nonidentity_entries(residual_v_a))

    native_orbits = {}
    for name, occurrence in (("p=x_97(t0)", p), ("q=x_76(s0)", q)):
        conjugates = []
        for exponent in range(7):
            actor = power(T, exponent)
            actor_inverse = power(T_inverse, exponent)
            conjugates.append(conjugate(actor, actor_inverse, occurrence))
        forward = identity
        reverse = identity
        for item in conjugates:
            forward = matrix_multiply(forward, item)
        for item in reversed(conjugates):
            reverse = matrix_multiply(reverse, item)
        assert matrices_equal(forward, identity)
        assert matrices_equal(reverse, identity)
        native_orbits[name[0]] = conjugates
        print(name, "forward and reverse seven-orbit products are identity")
        print(name, "orbit entries", [nonidentity_entries(item) for item in conjugates])

    cross_table = []
    for p_conjugate in native_orbits["p"]:
        row = []
        for q_conjugate in native_orbits["q"]:
            cross = commutator(
                p_conjugate, p_conjugate,
                q_conjugate, q_conjugate,
            )
            if matrices_equal(cross, identity):
                row.append(0)
            elif matrices_equal(cross, n):
                row.append(1)
            else:
                raise AssertionError(nonidentity_entries(cross))
        cross_table.append(tuple(row))
    print("cross commutator table ([p_k,q_l]=n^bit)")
    for row in cross_table:
        print(" ".join(map(str, row)))
    print("cross row weights", [sum(row) for row in cross_table])
    print("diagonal/offdiagonal weights",
          sum(cross_table[k][k] for k in range(7)),
          sum(cross_table[k][l] for k in range(7) for l in range(7) if k != l))

    q1_return = (
        root(9, 6, coeff("1", "1")),
    )
    assert full_signed_signature(q1_return, character) is None
    gauge_model()
    orbit_gauge_model()


if __name__ == "__main__":
    main()
