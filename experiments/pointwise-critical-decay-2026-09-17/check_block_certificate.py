"""Exact check of the diagonal-block certificate against pointwise gr-decay.

G = T_a x T_b (Cartesian product of regular trees, T_2 = Z), a <= b.
Degree D = a + b, so p_c >= p0 = 1/(D-1).  gr = b - 1 when b - 1 > a - 1
(and b >= 3).  Along the diagonal z_k = (x_k, y_k) with |x_k| = |y_k| = k,
|z_k| = 2k and tau_{p_c}(o, z_k) >= (2 p0^2 - p0^4)^k.  The pointwise bound
tau_{p_c}(o,z) <= gr^{-|z|} fails iff  ratio = gr^2 (2 p0^2 - p0^4) > 1,
since then tau_{p_c}(o,z_k) gr^{|z_k|} >= ratio^k -> infinity.

Run: python3 check_block_certificate.py
"""
from fractions import Fraction as F
from math import log


def ratio(a, b):
    D = a + b
    p0 = F(1, D - 1)
    block = 2 * p0**2 - p0**4
    gr = b - 1
    return gr, p0, block, gr * gr * block


def main():
    cases = [(3, 10, "(Z/2)^{*3} x (Z/2)^{*10}"),
             (2, 6, "Z x F_3"),
             (4, 12, "F_2 x F_6"),
             (4, 4, "F_2 x F_2 (no violation from this block)"),
             (2, 4, "Z x F_2 (no violation from this block)")]
    for a, b, name in cases:
        gr, p0, block, r = ratio(a, b)
        eps = log(r) / (2 * log(gr)) if r > 1 else 0.0
        print(f"T_{a} x T_{b}  [{name}]: gr={gr}, p0={p0}, block={block}, "
              f"gr^2*block={r} = {float(r):.6f}, violates={r > 1}, "
              f"pointwise exponent deficit eps={eps:.5f}")
    # smallest b for each a where the certificate violates
    for a in range(2, 9):
        b = a + 1
        while ratio(a, b)[3] <= 1:
            b += 1
        print(f"a={a}: smallest b with violation = {b}")


if __name__ == "__main__":
    main()
