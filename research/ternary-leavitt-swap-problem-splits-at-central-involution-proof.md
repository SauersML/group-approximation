---
rg: 2
id: ternary-leavitt-swap-problem-splits-at-central-involution-proof
kind: route
title: Average over the central involution and conjugate the swap by the sign unit
target: ternary-leavitt-swap-problem-splits-at-central-involution
requires: []
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

`(2(1 +- z))^2 = 2(1 +- z)` in characteristic three, and the two idempotents sum
to `4 = 1`. `d = s0 t0 - s1 t1` squares to `s0 t0 + s1 t1 = 1` and satisfies
`d w d = -w`, so on `S_-` it swaps `2(1 + w)` with `2(1 - w)`, the complement.
Matrix units follow, and a one-sided inverse through `E_11` in `M_2(T)` is a row
and a column over `T` whose products give the identity matrix, i.e. a Cohn family.
The Leavitt evaluation sends `z` to `-1` and `2(1 + z)` to `0`. Projecting
`c e b = 1` to `S_+` gives the equation over the scalar quotient. On
anti-invariant configurations a linear automaton depends only on the `S_-`
component, and those configurations form a proper subshift. That subshift is a
linear direct summand of the full shift, so a solution in `S_-` still gives a strict
automaton on the full shift (correction 7.4(e), gk-verify-pos, 2026-09-12). Section 7
of the artifact.

*Verification: earlier review by `gk-verify-pos`, Section 23 of `research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md` (parts 1–5 PASS; part 6 corrected forward). Independent re-derivation by `w4-vf-linear-b` (2026-09-12), Section 34 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS for parts 1–6 as now stated. Checked:*
- *the central idempotents, `(dw)d = zw`, the matrix units, and no commutative image;*
- *the Cohn-family form, and the projection to `S_+`;*
- *the padded pair `CA = 1 != AC`, and the embedding of `G` in `PG`.*
