"""Faithful exact audit of the B2 pairing on the full signed Hecke source.

Run only through MSI.  Unlike the older constant-arrow normalizer screen, this
checks all ten actual coefficient generators of L0 in sparse Leavitt matrices.
"""

from depth_one_paired_leavitt_return_search import multiply as coefficient_multiply
from endpoint_chain_center_hecke_collision_audit import (
    coeff, conjugate, root,
)
from signed_hecke_literal_pauli_probe_audit import matrices_equal, word_matrix


def main():
    q = coeff("1", "1")
    a1 = coeff("1", "0")
    a2 = coeff("1", "00")
    b2 = coeff("00", "1")
    b3 = coeff("000", "1")
    b3a1 = coefficient_multiply(b3, a1)

    named = {
        "C1": root(4, 2, q),
        "C2": root(5, 4, q),
        "C3": root(6, 5, q),
        "d": root(8, 2, b2),
        "f": root(9, 4, b3),
        "c": root(9, 7, b3a1),
        "k": root(9, 2, b3),
        "v": root(5, 7, a1),
        "w": root(6, 7, a1),
        "s": root(6, 8, a2),
        "r": root(5, 8, a2),
    }
    actors = {
        "r": ((8, 5, a2),),
        "B2": ((4, 8, b2),),
    }
    x52 = root(5, 2, q)
    x64 = root(6, 4, q)

    # r fixes every displayed generator except C3 -> C3*s and d -> d*x52.
    r_expected = {
        **{name: named[name] for name in named if name != "r"},
        "C3": word_matrix(((5, 6, q), (8, 6, a2))),
        "d": word_matrix(((2, 8, b2), (2, 5, q))),
    }
    # B2 fixes every displayed generator except C1 -> C1*d and s -> s*x64.
    b2_expected = {
        **{name: named[name] for name in named if name != "r"},
        "C1": word_matrix(((2, 4, q), (2, 8, b2))),
        "s": word_matrix(((8, 6, a2), (4, 6, q))),
    }
    for actor_name, expected in (("r", r_expected), ("B2", b2_expected)):
        for name in ("C1", "C2", "C3", "d", "f", "c", "k", "v", "w", "s"):
            assert matrices_equal(
                conjugate(actors[actor_name], named[name]), expected[name]
            )
        print(actor_name, "normalizes (L0,lambda0)", flush=True)

    # Both corrections in the r table are positive: s is a positive L0
    # generator and x52 is a positive derived H-root.  Likewise d and x64 are
    # positive in the B2 table.  Thus the direct tables preserve lambda0.
    assert matrices_equal(x52, word_matrix(((2, 5, q),)))
    assert matrices_equal(x64, word_matrix(((4, 6, q),)))

    b2_r = conjugate(actors["B2"], named["r"])
    assert matrices_equal(b2_r, word_matrix(
        ((8, 5, a2), (4, 5, q))
    ))
    print("B2 r B2^-1 = r C2", flush=True)
    print("CONSEQUENCE: on Q, B2 exchanges the r=+ and r=- projections",
          flush=True)


if __name__ == "__main__":
    main()
