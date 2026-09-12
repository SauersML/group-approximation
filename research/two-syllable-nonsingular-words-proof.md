---
rg: 2
id: two-syllable-nonsingular-words-proof
kind: route
title: Twisted 2-cycle and the AB=BA=L construction solve c0 t c1 t c2
target: two-syllable-nonsingular-words-are-exactly-solvable
requires:
  - rgr-p-reduces-to-cyclic-twist-system
  - scalar-target-power-words-have-exact-roots
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
---

Proof of `two-syllable-nonsingular-words-are-exactly-solvable` (artifact Section 3).

Amplify by `e = 2`. Write `t = [[0, b_1], [b_0, 0]]` on `W_0 (+) W_1` (so `t(w_0, w_1) = (b_1 w_1,
b_0 w_0)`), `c_i (x) 1_2 = diag(c_i, c_i)`. Direct block multiplication of `c_0 t c_1 t c_2` gives

```text
c_0 t c_1 t c_2 = diag( c_0 b_1 c_1 b_0 c_2 ,  c_0 b_0 c_1 b_1 c_2 ) = diag(P_0, P_1).
```

Set `K = c_0^(-1) lambda c_2^(-1)`. Then `P_0 = P_1 = lambda 1` iff `b_1 c_1 b_0 = b_0 c_1 b_1 = K`.
Put `A = c_1 b_0`, `B = c_1 b_1`; the pair becomes `B A = A B = c_1 K`. Choosing `A = 1`, `B = c_1 K`
gives `b_0 = c_1^(-1)`, `b_1 = K`. Verify: `b_1 c_1 b_0 = K c_1 c_1^(-1) = K` and `b_0 c_1 b_1 =
c_1^(-1) c_1 K = K`; substituting, `P_0 = c_0 K c_1 c_1^(-1) c_2 = lambda 1` and `P_1 = c_0 c_1^(-1) c_1
K c_2 = lambda 1`. Since `b_0, b_1 in GL_d`, `t in GL_(2d)`. QED.

Equal-exponent reduction: `u = t^(e')` solves `u c_1 u = K`; set `v = c_1 u`, then `v^2 = c_1 K`, an
e-th/square root handled by the established power-word result (`scalar-target-power-words-have-exact-roots`
for the scalar pieces, the general power case for the matrix `c_1 K`), and `t` is an `e'`-th root of `u`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 30.3 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the block values `P_0 = c_0 b_1 c_1 b_0 c_2` and `P_1 = c_0 b_0 c_1 b_1 c_2`, and the choice `b_0 = c_1^-1`, `b_1 = K`;*
- *the general power word `t^m = M`, solvable exactly after amplification by `p^r` via binomial roots and `(1 + N_(p^r s))^(p^r) ~ ⊕^(p^r) (1 + N_s)`.*

*So the equal-exponent reduction holds.*
