"""Cross-check x_59(1) against the endpoint/order-five mixed cell.

Run only through MSI.  The search is deliberately bounded: besides exact
orders and signed-source intersections it enumerates reduced words in W,M
only through length eight.  Sparse Leavitt matrices are compared exactly;
no finite-prefix truncation is used.
"""

from collections import deque

from endpoint_chain_center_hecke_collision_audit import coeff, entries, root, whitehead
from signed_hecke_literal_pauli_probe_audit import (
    constant_matrix,
    identity_matrix,
    inverse_word_matrix,
    matrices_equal,
    matrix_key,
    matrix_multiply,
    word_matrix,
)
from signed_hecke_root_normalizer_audit import signed_l0


def multiply(*matrices):
    answer = identity_matrix()
    for matrix in matrices:
        answer = matrix_multiply(answer, matrix)
    return answer


IDENTITY = identity_matrix()
IDENTITY_KEY = matrix_key(IDENTITY)


def power(matrix, exponent):
    answer = IDENTITY
    for _ in range(exponent):
        answer = matrix_multiply(answer, matrix)
    return answer


def order(matrix, bound=10000):
    current = IDENTITY
    for exponent in range(1, bound + 1):
        current = matrix_multiply(current, matrix)
        if matrices_equal(current, IDENTITY):
            return exponent
    return None


def conjugate(actor, actor_inverse, element):
    return multiply(actor, element, actor_inverse)


def commutator(left, left_inverse, right, right_inverse):
    return multiply(left, right, left_inverse, right_inverse)


def entry_digest(matrix, limit=8):
    digest = []
    for target, source, coefficient in entries(matrix):
        terms = tuple(sorted(coefficient))
        digest.append((target, source, len(terms), terms[:4]))
    return len(digest), tuple(digest[:limit])


def main():
    one = coeff("", "")
    a2 = coeff("1", "00")
    b3 = coeff("000", "1")

    words = {
        "W": whitehead(8, 2, 2),
        # word tuples are (source,target,coefficient), so the native
        # J_2=x_98(x_2)x_89(y_2)x_98(x_2) is whitehead(8,9,2).
        "J2": whitehead(8, 9, 2),
        "A2": ((8, 5, a2),),
        "B3": ((5, 9, b3),),
        "n": ((9, 5, one),),
    }
    words["M"] = words["J2"] + words["B3"] + words["A2"]
    words["C"] = words["W"] + words["M"]
    matrices = {name: word_matrix(word) for name, word in words.items()}
    inverses = {
        name: inverse_word_matrix(word) for name, word in words.items()
    }

    print("claimed relation checks")
    m7 = power(matrices["M"], 7)
    c5 = power(matrices["C"], 5)
    print("M^7=1", matrices_equal(m7, IDENTITY), "digest", entry_digest(m7), flush=True)
    print("C^5=1", matrices_equal(c5, IDENTITY), "digest", entry_digest(c5), flush=True)

    print("commutation with n")
    for name in ("W", "J2", "A2", "B3", "M", "C"):
        commute = matrices_equal(
            multiply(matrices[name], matrices["n"]),
            multiply(matrices["n"], matrices[name]),
        )
        bracket = commutator(
            matrices["n"], inverses["n"], matrices[name], inverses[name]
        )
        print(name, "commutes", commute, "commutator identity",
              matrices_equal(bracket, IDENTITY))

    print("conjugates of n (faithful coefficient entries)")
    for name in ("W", "J2", "A2", "B3", "M", "C"):
        image = conjugate(matrices[name], inverses[name], matrices["n"])
        print(name, entries(image), flush=True)

    ncn = conjugate(matrices["n"], matrices["n"], matrices["C"])
    cyclic_match = tuple(
        k for k in range(5) if matrices_equal(ncn, power(matrices["C"], k))
    )
    print("n C n in <C> powers", cyclic_match)
    print("(n C^k)^2 identities", tuple(
        matrices_equal(power(multiply(matrices["n"], power(matrices["C"], k)), 2), IDENTITY)
        for k in range(1, 5)
    ))

    actor_signed = signed_l0()
    l0 = {
        matrix_key(constant_matrix(actor)): sign
        for actor, sign in actor_signed.items()
    }
    assert len(l0) == 8192
    print("signed source intersections")
    for actor_name in ("M", "C"):
        actor = matrices[actor_name]
        actor_inverse = inverses[actor_name]
        intersection = []
        conflicts = 0
        for key, sign in l0.items():
            element = [list(row) for row in key]
            image_key = matrix_key(conjugate(actor, actor_inverse, element))
            moved_sign = l0.get(image_key)
            if moved_sign is not None:
                intersection.append(key)
                conflicts += sign != moved_sign
        print(actor_name, "intersection", len(intersection), "sign conflicts", conflicts)

    generators = {
        "W": (matrices["W"], matrices["W"]),
        "M": (matrices["M"], inverses["M"]),
        "m": (inverses["M"], matrices["M"]),
    }
    queue = deque([(IDENTITY, IDENTITY, "")])
    seen = {IDENTITY_KEY}
    hits = []
    maximum_length = 8
    while queue:
        current, current_inverse, word = queue.popleft()
        if matrices_equal(current, matrices["n"]):
            hits.append(word)
        if len(word) >= maximum_length:
            continue
        for letter, (generator, generator_inverse) in generators.items():
            if word and ((word[-1] == "W" and letter == "W") or
                         (word[-1], letter) in (("M", "m"), ("m", "M"))):
                continue
            nxt = multiply(current, generator)
            nxt_key = matrix_key(nxt)
            if nxt_key in seen:
                continue
            seen.add(nxt_key)
            queue.append((
                nxt,
                multiply(generator_inverse, current_inverse),
                word + letter,
            ))
    print("bounded <W,M> search", "depth", maximum_length, "states", len(seen), "n hits", hits)

    orbit = []
    for k in range(5):
        ck = power(matrices["C"], k)
        cki = power(matrices["C"], (-k) % 5)
        orbit.append(conjugate(ck, cki, matrices["n"]))
    print("C-orbit size of n", len({matrix_key(element) for element in orbit}))
    orbit_product = IDENTITY
    for element in orbit:
        orbit_product = multiply(orbit_product, element)
    print("ordered C-orbit product identity", matrices_equal(orbit_product, IDENTITY))


if __name__ == "__main__":
    main()
