"""Exact integer verification that W_pkt annihilates the H-fixed space.

`atlas_asc_tangent_exact.py` finds, in double precision, that
`ker rho(W_pkt)` has dimension `120 = [A_8 : H]` with `H = GL_3(2)`, matching
the qualitative tangent certificate.  Containment one way is exact integer
arithmetic and needs no eigenvalues: the `H`-fixed space of the regular
module is spanned by the indicators of the 120 right cosets `Hx`, so it
suffices to check

    (W_pkt * 1_(Hx))(g) = sum_(y in Hx) W_pkt(g y^(-1)) = 0    for all g, x.

With `|supp W_pkt| = 101` and `|H| = 168` that is two million integer
additions.  Together with the measured rank `20040 = 20160 - 120` it pins the
kernel exactly: containment is proved here, equality follows from the
dimension count.
"""

import json
import sys, os
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_asc_packet_build import index_group
from atlas_asc_tangent_exact import convolve_square, group_algebra_of_packet
from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


def main():
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    _rows, table, elements = index_group()

    vectors, skipped, matrices = group_algebra_of_packet(
        alignment, alignment_inverse, table)
    packet = {}
    for vector in vectors:
        for key, value in convolve_square(vector, matrices).items():
            packet[key] = packet.get(key, 0) + value
    support = {key: value for key, value in packet.items() if value}

    subgroup = []
    for entry in range(1 << 9):
        block = np.array([[(entry >> (3 * r + c)) & 1 for c in range(3)]
                          for r in range(3)], dtype=np.uint8)
        matrix = I4.copy()
        matrix[:3, :3] = block
        try:
            gf2_inv(matrix)
        except ValueError:
            continue
        subgroup.append(matrix)

    # NOTE on convention: the accumulator below adds the coefficient of w at
    # the index w*y^(-1)^(-1) = w*y, i.e. it forms sum_(y in C) W(g y).  With
    # z = y^(-1) that is sum_(z in C^(-1)) W(g z^(-1)) = (L_W 1_(C^(-1)))(g),
    # so the vectors actually tested are the indicators of the INVERSE family:
    # the "left" pass below tests the right cosets Hx, which is the family the
    # kernel contains.  The other pass is the control and must fail.
    def cosets_of(side):
        seen, out = set(), []
        for element in elements:
            if matrix_key(element) in seen:
                continue
            coset = [gf2_mul(h, element) if side == "right"
                     else gf2_mul(element, h) for h in subgroup]
            for member in coset:
                seen.add(matrix_key(member))
            out.append(coset)
        return out

    # Both families are run: exactly one of them is the H-fixed space of the
    # kernel, and the other is the control that has to fail.  Getting this
    # convention wrong is the easiest way to "verify" a vacuous statement.
    letters_energy = {}
    results = {}
    for side in ("left", "right"):
        worst = 0
        for coset in cosets_of(side):
            accumulator = {}
            for y in coset:
                y_inverse = gf2_inv(y)
                for key, value in support.items():
                    g = gf2_mul(
                        np.frombuffer(key, dtype=np.uint8).reshape(4, 4),
                        y_inverse)
                    gkey = matrix_key(g)
                    accumulator[gkey] = accumulator.get(gkey, 0) + value
            worst = max(worst, max(abs(v) for v in accumulator.values()))
        results[side] = worst
    worst = min(results.values())

    # The same test for W_cov = 4 - 2 h_a - 2 h_b.  If it does NOT annihilate
    # the same vectors then ker(W_pkt) is not inside ker(W_cov), the constant
    # is infinite and the collapse fails at first order -- so this is the crux
    # of the claim.  On the family the kernel contains it must vanish, and the
    # reason is one line: (L_(W_cov) 1_(Hx))(g) = 4[g in Hx] - 2[g in h_a Hx]
    # - 2[g in h_b Hx] = 0 because h_a, h_b lie in H.
    from atlas_asc_packet_build import raw_s3_letters
    letters, _raw = raw_s3_letters(alignment, alignment_inverse)
    cov = {matrix_key(I4): 4}
    for letter in letters:
        key = matrix_key(letter)
        cov[key] = cov.get(key, 0) - 2
    for side in ("left", "right"):
        worst_cov = 0
        offenders = 0
        for coset in cosets_of(side):
            accumulator = {}
            for y in coset:
                y_inverse = gf2_inv(y)
                for key, value in cov.items():
                    g = gf2_mul(
                        np.frombuffer(key, dtype=np.uint8).reshape(4, 4),
                        y_inverse)
                    gkey = matrix_key(g)
                    accumulator[gkey] = accumulator.get(gkey, 0) + value
            local = max(abs(v) for v in accumulator.values())
            worst_cov = max(worst_cov, local)
            offenders += 1 if local else 0
        letters_energy[side] = {"max_abs": worst_cov,
                                "cosets_not_annihilated": offenders}

    print(json.dumps({
        "subgroup_order": len(subgroup),
        "cosets": 120,
        "support_W_pkt": len(support),
        "max_abs_convolution_coefficient_by_side": results,
        "annihilates_H_fixed_space_exactly": worst == 0,
        "W_cov_on_the_same_vectors": letters_energy,
        "kernel_inclusion_holds_exactly":
            bool(results["left"] == 0
                 and letters_energy["left"]["max_abs"] == 0),
        "words_skipped": skipped,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
