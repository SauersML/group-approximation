"""Exact short-word audit around the unique endpoint fine collision.

Run only through MSI.  The Leavitt calculation is kept sparse by conjugating
one elementary/Whitehead factor at a time.  The final four-bit enumeration
is the exact action on the commuting row-6 root group
<C3,s,t,sprime> rather than a truncation of the Leavitt module.
"""

from endpoint_chain_center_hecke_collision_audit import (
    coeff, conjugate, entries, generated_signed, group_lookup, root,
    whitehead,
)
from depth_one_paired_leavitt_return_search import (
    multiply as coefficient_multiply,
)
from signed_hecke_literal_pauli_probe_audit import (
    matrices_equal, matrix_multiply, word_matrix,
)


def conjugate_by_factors(factors, matrix):
    """Conjugate by the product factors[0]...factors[-1]."""
    answer = matrix
    for factor in reversed(factors):
        answer = conjugate(factor, answer)
    return answer


def bit_apply(matrix, vector):
    answer = 0
    while vector:
        lowest = vector & -vector
        answer ^= matrix[lowest.bit_length() - 1]
        vector ^= lowest
    return answer


def bit_multiply(left, right):
    return tuple(bit_apply(left, column) for column in right)


def bit_power(matrix, exponent):
    answer = (1, 2, 4, 8)
    for _ in range(exponent):
        answer = bit_multiply(answer, matrix)
    return answer


def bit_group(generators):
    identity = (1, 2, 4, 8)
    seen = {identity}
    frontier = [identity]
    while frontier:
        current = frontier.pop()
        for generator in generators:
            nxt = bit_multiply(current, generator)
            if nxt not in seen:
                seen.add(nxt)
                frontier.append(nxt)
    return seen


def bit_words(generators):
    """Shortest positive words in the named finite generators."""
    identity = (1, 2, 4, 8)
    words = {identity: ""}
    frontier = [identity]
    for current in frontier:
        for name, generator in generators:
            nxt = bit_multiply(current, generator)
            if nxt not in words:
                words[nxt] = words[current] + name
                frontier.append(nxt)
    return words


def main():
    q = coeff("1", "1")
    a1 = coeff("1", "0")
    a2 = coeff("1", "00")
    a3 = coeff("1", "000")
    b2 = coeff("00", "1")
    b3 = coeff("000", "1")
    b3a1 = coefficient_multiply(b3, a1)

    named = {
        "C1": root(4, 2, q),
        "C2": root(5, 4, q),
        "C3": root(6, 5, q),
        "v": root(5, 7, a1),
        "w": root(6, 7, a1),
        "s": root(6, 8, a2),
        "t": root(6, 9, a3),
        "sprime": root(6, 2, a3),
        "A1": root(4, 7, a1),
        "A2": root(5, 8, a2),
        "A2prime": root(5, 2, a3),
        "B2": root(8, 4, b2),
        "B3": root(9, 5, b3),
        "Bsource": root(8, 3, b2),
        "Bendpoint": root(2, 3, b3),
        "D53": root(5, 3, q),
        "d": root(8, 2, b2),
        "f": root(9, 4, b3),
        "k": root(9, 2, b3),
        "c": root(9, 7, b3a1),
    }
    w_word = whitehead(8, 2, 2)
    a2_word = ((8, 5, a2),)
    b3_word = ((5, 9, b3),)
    # whitehead(r,s,m) transports the active endpoint r to s; the native
    # J2=x_98(x2)x_89(y2)x_98(x2) is therefore whitehead(8,9,2).
    j2_word = whitehead(8, 9, 2)
    j1_word = whitehead(7, 8, 1)
    named["J1"] = word_matrix(j1_word)
    named["J2"] = word_matrix(j2_word)
    m_factors = (j2_word, b3_word, a2_word)

    print("W conjugates")
    for name in ("C1", "C2", "C3", "v", "w", "s", "t", "sprime",
                 "A2", "A2prime"):
        print(name, entries(conjugate(w_word, named[name])), flush=True)

    assert matrices_equal(conjugate(w_word, named["s"]), named["sprime"])
    assert matrices_equal(conjugate(w_word, named["A2"]), named["A2prime"])
    assert matrices_equal(conjugate(w_word, named["Bsource"]),
                          named["Bendpoint"])

    print("M=J2*B3*A2 conjugates")
    m_images = {}
    for name in ("C1", "C2", "C3", "v", "w", "s", "t", "sprime"):
        image = conjugate_by_factors(m_factors, named[name])
        m_images[name] = image
        print(name, entries(image), flush=True)

    assert matrices_equal(m_images["s"], named["t"])
    assert matrices_equal(m_images["sprime"], named["sprime"])
    assert matrices_equal(m_images["w"], named["w"])

    k1_names = ("C1", "C2", "C3", "v", "w")
    k1 = generated_signed(tuple(
        (named[name], name.startswith("C")) for name in k1_names
    ))
    assert group_lookup("K1-odd-mixed", k1, m_images["C2"]) is None
    print("M normalizes signed K1", False, flush=True)
    print("nonzero M powers normalizing signed K1", (), flush=True)

    # The two orders of the shortest mixed word have different endpoint
    # detector returns.  W*A2 picks up the literal returned q-root D53,
    # while A2*W is the bare endpoint transport.
    wa2_bsource = conjugate_by_factors((w_word, a2_word), named["Bsource"])
    a2w_bsource = conjugate_by_factors((a2_word, w_word), named["Bsource"])
    endpoint_with_d53 = matrix_multiply(named["Bendpoint"], named["D53"])
    assert matrices_equal(wa2_bsource, endpoint_with_d53)
    assert matrices_equal(a2w_bsource, named["Bendpoint"])
    print("W*A2 sends Bsource to", entries(wa2_bsource), flush=True)
    print("A2*W sends Bsource to", entries(a2w_bsource), flush=True)

    # On V=<C3,s,t,sprime>, columns encode images in the ordered basis.
    # Exact sparse conjugation above gives
    # M: C3->C3*t, s->t, t->C3*s, sprime->sprime;
    # W: C3->C3, s->sprime, t->t, sprime->s.
    m_action = (1 ^ 4, 4, 1 ^ 2, 8)
    w_action = (1, 8, 4, 2)
    identity_action = (1, 2, 4, 8)
    assert bit_power(m_action, 7) == identity_action
    assert bit_power(w_action, 2) == identity_action
    assert bit_power(bit_multiply(w_action, m_action), 5) == identity_action
    actor = bit_group((m_action, w_action))
    assert len(actor) == 20160
    assert len({bit_apply(g, 1) for g in actor}) == 15
    print("four-bit actor order", len(actor), flush=True)
    print("nonzero orbit size",
          len({bit_apply(g, 1) for g in actor}), flush=True)
    print("orders W,M,W*M", 2, 7, 5, flush=True)

    # Screen the eight GL4 actors which fix C3 and s while shearing
    # sprime by C3.  Such an actor would pair the two sprime signs inside
    # the fine source if its exact Leavitt lift normalized signed K1.
    words = bit_words((("W", w_action), ("M", m_action)))
    returning = sorted(
        ((action, word) for action, word in words.items()
         if action[0] == 1
         and all((action[column] & 1) == 0 for column in (1, 2, 3))),
        key=lambda item: (len(item[1]), item[1]),
    )
    assert len(returning) == 168
    complement_orbit = {
        bit_apply(action, 2) for action, _ in returning
    }
    assert complement_orbit == {2, 4, 6, 8, 10, 12, 14}
    print("signed-K1 returning actor count", len(returning), flush=True)
    print("returning complement nonzero orbit", len(complement_orbit),
          flush=True)
    shear_words = sorted(
        (word for action, word in words.items()
         if action[0] == 1 and action[1] == 2 and action[3] == (1 ^ 8)),
        key=lambda word: (len(word), word),
    )
    assert len(shear_words) == 8
    print("C3,s-fixed sprime shears", tuple(shear_words), flush=True)

    def exact_conjugate(actor_word, matrix):
        answer = matrix
        for letter in reversed(actor_word):
            if letter == "W":
                answer = conjugate(w_word, answer)
            else:
                answer = conjugate_by_factors(m_factors, answer)
        return answer

    # The full common Hecke source has four further positive generators.
    # Block support leaves at most one nontrivial GL4 return: on the root
    # coordinates it fixes C3,s,sprime and shears t by sprime.  Print the
    # literal lift on all ten L0 generators.  Full 8192-element collection is
    # deliberately avoided here; it is slower than the bounded signal needed
    # for this audit and the displayed exact images decide pointwise return.
    full_l0_names = ("C1", "C2", "C3", "d", "f", "c", "k", "v", "w", "s")
    q_return_words = sorted(
        (word for action, word in returning
         if action == (1, 2, 4 ^ 8, 8)),
        key=lambda word: (len(word), word),
    )
    assert len(q_return_words) == 1
    q_return_word = q_return_words[0]
    q_return_fixed = []
    for name in full_l0_names:
        image = exact_conjugate(q_return_word, named[name])
        q_return_fixed.append(matrices_equal(image, named[name]))
        print("full-L0 return conjugates", name, "to", entries(image),
              flush=True)
    print("full-L0 block-return word", q_return_word, flush=True)
    print("full-L0 block-return fixes generators",
          tuple(q_return_fixed), flush=True)

    # Audit a shortest literal signed-source return which transports the
    # fine root s to the adjacent depth-three root t.  This is the smallest
    # candidate for upgrading the character-orbit argument to an actual
    # same-Q native-cell occurrence.
    s_to_t_returns = sorted(
        (word for action, word in returning if bit_apply(action, 2) == 4),
        key=lambda word: (len(word), word),
    )
    assert s_to_t_returns
    shortest_s_to_t = s_to_t_returns[0]
    print("shortest signed-K1 return s->t", shortest_s_to_t, flush=True)
    for name in ("C1", "C2", "C3", "v", "w", "s", "t", "sprime",
                 "A1", "A2", "B2", "B3", "J1", "J2"):
        image = exact_conjugate(shortest_s_to_t, named[name])
        print("return", shortest_s_to_t, "conjugates", name, "to",
              entries(image), flush=True)

    # The 168 returns are exactly diag(1,GL3) on the four active summands.
    # Hence they fix K1 pointwise: C2 and v use active target 1, C3 uses
    # active source 1, w is disjoint, and C1 uses the q-part of coordinate 2,
    # orthogonal to the active e3-part there.  The other 19992 actors fail
    # one of the first-column/first-row tests before any long-word expansion.

    signed_shear_returns = []
    for actor_word in shear_words:
        signed = True
        for name in k1_names:
            image = exact_conjugate(actor_word, named[name])
            sign = group_lookup("K1-odd-mixed", k1, image)
            if sign is None or sign != name.startswith("C"):
                signed = False
                break
        if signed:
            signed_shear_returns.append(actor_word)
    print("signed-K1-normalizing shear words",
          tuple(signed_shear_returns), flush=True)

    coarse = tuple(x for x in range(16) if x & 1)
    fine = tuple(x for x in coarse if not (x & 2))
    meet = tuple(x for x in fine if not (x & 8))
    print("C3-negative/fine/meet character counts",
          len(coarse), len(fine), len(meet), flush=True)
    print("returning-GL3 multiplicity formula",
          "p2=m0+3*m1, meet=m0+m1, ratio>=1/3", flush=True)


if __name__ == "__main__":
    main()
