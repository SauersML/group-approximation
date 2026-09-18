---
rg: 2
id: sl3-congruence-transfer-kills-abelianization
kind: claim
title: For n >= 3 and d >= 2 the transfer from the abelianization of Γ_n(d) to that of Γ_n(d^2) is zero, so the congruence odometer groupoid of SL_n(Z) has no integral first homology
distinct_from:
  matrix-corner-laurent-rings-block-fp-elementary-groups: that kills crossed products whose chain contains an indicable subgroup; this computes the torsion abelianizations along the congruence chain of SL_n(Z), n >= 3, where no subgroup is indicable, and shows their classes die under transfer.
artifacts:
  - research/artifacts/gq-deep-adelic-1-sl3-remnant.md
---

**ESTABLISHED** by `sl3-congruence-transfer-kills-abelianization-proof` (lane proof, not
independently reviewed). Its one external input is Lee–Szczarba, quoted below.

## Input (Lee–Szczarba)

Write `Γ_d = Γ_d(n) = ker(SL_n(Z) -> SL_n(Z/d))`. Imoto–Kobayashi, arXiv:2212.13181v2, Theorem 1.1,
attributed to R. Lee and R. H. Szczarba, *On the homology and cohomology of congruence subgroups*,
Invent. Math. 33 (1976), 15–53. As fetched (the HTML rendering; the primary was not read):

> "For n≥3 and d≥1, the abelianization of Γd(n) is isomorphic to (ℤ/dℤ)^{n²−1}."

The sentence before it records that Lee–Szczarba "constructed an epimorphism
Γd(n)→(ℤ/dℤ)^{n²−1} whose kernel is Γ_{d²}(n)".

**What is used.** `θ_d(I + dA) = A mod d` is a homomorphism `Γ_d -> M_n(Z/d)` with kernel `Γ_(d^2)`,
by `(I+dA)(I+dB) = I + d(A+B) + d^2 AB`. Its image lies in the trace-zero matrices `sl_n(Z/d)`, since
`det(I + dA) ≡ 1 + d·tr(A) mod d^2`. The quoted order `d^(n²-1)` of the abelianization, together with
the abelian quotient `Γ_d/Γ_(d^2)`, gives:
- `[Γ_d, Γ_d] = Γ_(d^2)`;
- `θ_d` induces `Γ_d^ab ≅ sl_n(Z/d)`.

## Statement

Let `n >= 3` and `d >= 2`.
1. The transfer `V : Γ_d^ab -> Γ_(d^2)^ab` is the zero map.
2. **Consequence.** For every `d`, the transfer `Γ_d^ab -> Γ_e^ab` is zero whenever `d^2 | e`, since
   transfers compose. So the direct limit of `H_1(Γ_d; Z)` along transfer maps, over the congruence
   levels ordered by divisibility, is `0`. By Shapiro's lemma, applied to
   `C(SL_n(Ẑ), Z) = colim_d Z[Γ/Γ_d]` (standard, not written out), this is
   `H_1(SL_n(Z); C(SL_n(Ẑ), Z)) = 0`: the transformation groupoid of the congruence odometer has
   vanishing integral `H_1`.

## Use

In crossed-product rings over the congruence odometer (or a Toeplitz extension of it), the
"torsion index units" of risk R2 are the units `χ_C u_γ + (1 - χ_C)` with `C` a block of level `d` and
`γ ∈ Γ_d`. Part 1 makes their `K_1` classes signs after one Morita step to level `d^2`. See
`sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`, part 6.
