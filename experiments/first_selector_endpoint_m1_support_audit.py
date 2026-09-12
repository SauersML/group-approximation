"""Faithful sparse audit of the first endpoint actor on the signed p2 source.

Run only through MSI.  The finite four-bit screen is the literal projective
GL4 block; only its sixteen possible signed-source returns are replayed in
the Leavitt matrices.
"""

from endpoint_chain_center_hecke_collision_audit import (
    coeff, conjugate, entries, generated_signed, group_lookup, root,
    whitehead,
)
from endpoint_fine_collision_odd_mixed_audit import (
    bit_apply, bit_group, bit_multiply, bit_power, bit_words,
    conjugate_by_factors,
)
from signed_hecke_literal_pauli_probe_audit import matrices_equal, word_matrix


def main():
    q = coeff("1", "1")
    a1 = coeff("1", "0")
    a2 = coeff("1", "00")
    b2 = coeff("00", "1")

    named = {
        "C1": root(4, 2, q),
        "C2": root(5, 4, q),
        "C3": root(6, 5, q),
        "v": root(5, 7, a1),
        "w": root(6, 7, a1),
        "s": root(6, 8, a2),
        "r": root(5, 8, a2),
        "vprime": root(5, 2, a2),
        "wprime": root(6, 2, a2),
        "h": root(6, 4, q),
    }

    # W0 swaps e1@7 with e2@2.  M1 is the native Singer head on
    # q@4,e1@7,e2@8.
    w0_word = whitehead(7, 2, 1)
    j1_word = whitehead(7, 8, 1)
    b2_word = ((4, 8, b2),)
    a1_word = ((7, 4, a1),)
    m1_factors = (j1_word, b2_word, a1_word)

    print("W0 conjugates first row")
    for name in ("C2", "v", "r", "vprime"):
        print(name, entries(conjugate(w0_word, named[name])), flush=True)
    print("M1 conjugates first row")
    m1_images = {}
    for name in ("C2", "v", "r", "vprime"):
        image = conjugate_by_factors(m1_factors, named[name])
        m1_images[name] = image
        print(name, entries(image), flush=True)

    assert matrices_equal(conjugate(w0_word, named["v"]), named["vprime"])
    assert matrices_equal(conjugate(w0_word, named["r"]), named["r"])
    assert matrices_equal(conjugate(w0_word, named["C2"]), named["C2"])
    assert matrices_equal(conjugate(w0_word, named["vprime"]), named["v"])
    assert matrices_equal(m1_images["C2"], word_matrix(
        ((4, 5, q), (8, 5, a2))
    ))
    assert matrices_equal(m1_images["v"], named["r"])
    assert matrices_equal(m1_images["r"], word_matrix(
        ((4, 5, q), (7, 5, a1))
    ))
    assert matrices_equal(m1_images["vprime"], named["vprime"])

    # Columns are images in (C2,v,r,vprime).  They are the same Singer plus
    # endpoint-swap matrices as in the established second-selector GL4 block.
    m_action = (1 ^ 4, 4, 1 ^ 2, 8)
    w_action = (1, 8, 4, 2)
    identity = (1, 2, 4, 8)
    assert bit_power(m_action, 7) == identity
    assert bit_power(w_action, 2) == identity
    assert bit_power(bit_multiply(w_action, m_action), 5) == identity
    actor = bit_group((m_action, w_action))
    assert len(actor) == 20160
    print("first endpoint actor order", len(actor), flush=True)

    # A signed-p2 return must preserve the first-row signed plane
    # <C2,v>, the second-row positive plane <w,s>, and the active target of
    # C1.  In the covector action this is precisely the displayed column
    # pattern.  There are only sixteen such GL4 matrices.
    words = bit_words((("W", w_action), ("M", m_action)))
    candidates = []
    for action, word in words.items():
        c0, c1, c2, c3 = action
        first_signed = c0 in (1, 3) and c1 == 2
        second_positive = c1 == 2 and c2 in (4, 6)
        c1_target_fixed = (c3 & 1) == 0
        if first_signed and second_positive and c1_target_fixed:
            candidates.append((action, word))
    candidates.sort(key=lambda item: (len(item[1]), item[1]))
    assert len(candidates) == 16
    print("projective signed-p2 return candidates", len(candidates), flush=True)

    k2_names = ("C1", "C2", "C3", "v", "w", "s")
    k2 = generated_signed(tuple(
        (named[name], name.startswith("C")) for name in k2_names
    ))

    def exact_conjugate(actor_word, matrix):
        answer = matrix
        for letter in reversed(actor_word):
            if letter == "W":
                answer = conjugate(w0_word, answer)
            else:
                answer = conjugate_by_factors(m1_factors, answer)
        return answer

    # The sixteen candidates form a subgroup.  Replay only a greedy finite
    # generating set; covariance then proves the exact assertion for every
    # return and avoids expanding sixteen unrelated shortest words.
    candidate_actions = {action for action, _ in candidates}
    return_generators = []
    generated_actions = {identity}
    for action, actor_word in candidates:
        if action not in generated_actions:
            return_generators.append((action, actor_word))
            generated_actions = bit_group(tuple(
                generator for generator, _ in return_generators
            ))
    assert generated_actions == candidate_actions
    print("signed-p2 return generators",
          tuple(word for _, word in return_generators), flush=True)

    r_profiles = []
    for action, actor_word in return_generators:
        signed = True
        for name in k2_names:
            image = exact_conjugate(actor_word, named[name])
            sign = group_lookup("first-selector-K2", k2, image)
            if sign is None or sign != name.startswith("C"):
                signed = False
                break
        assert signed
        r_image = exact_conjugate(actor_word, named["r"])
        r_profiles.append((actor_word, action[2], entries(r_image)))

    assert {action[2] for action, _ in candidates} == {4, 6}
    # The only possibilities are r and rv.  Since v=+1 on p2, both preserve
    # the r sign and neither pairs q1 with its complement.
    for action, actor_word in return_generators:
        r_image = exact_conjugate(actor_word, named["r"])
        expected = named["r"] if action[2] == 4 else word_matrix(
            ((8, 5, a2), (7, 5, a1))
        )
        assert matrices_equal(r_image, expected)

    print("exact signed-p2 return subgroup", len(candidate_actions), flush=True)
    print("r images in bit coordinates",
          tuple(sorted({action[2] for action, _ in candidates})), flush=True)
    print("generator return profiles", tuple(r_profiles), flush=True)
    print("VERDICT: every return sends r to r or r*v; p2 sees the same r sign",
          flush=True)

    # The literal B2 factor itself is not a K2 return: it sends C1 outside K2.
    # On the finer source L0 the missing correction d is present and positive;
    # `center-chain-mixed-hecke-overlap-is-common-pauli-source` proves that B2
    # normalizes its signed projection Q.  The faithful calculation below
    # verifies the other load-bearing identity: B2 flips r by the negative
    # source root C2.
    b2_r = conjugate(b2_word, named["r"])
    assert matrices_equal(b2_r, word_matrix(
        ((8, 5, a2), (4, 5, q))
    ))
    assert group_lookup("first-selector-K2", k2,
                        conjugate(b2_word, named["C1"])) is None
    print("B2 normalizes coarse signed K2", False, flush=True)
    print("B2 sends r to", entries(b2_r), flush=True)
    print("WITH ESTABLISHED FULL-Q NORMALIZATION: B2 swaps its r-sign halves",
          flush=True)


if __name__ == "__main__":
    main()
