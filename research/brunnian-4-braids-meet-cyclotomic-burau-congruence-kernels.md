---
rg: 2
id: brunnian-4-braids-meet-cyclotomic-burau-congruence-kernels
kind: claim
title: "For every product g of cyclotomic polynomials some nontrivial Brunnian 4-braid has Burau matrix congruent to I modulo (t−1)^2 g"
distinct_from:
  burau-minus-one-kernel-meets-brunnian-four-braids: that claim is the single modulus t+1; this claim covers every product of cyclotomic polynomials (other roots of unity and higher-order jets), with the extra factor (t−1)^2
  four-strand-burau-representation-has-nontrivial-kernel: that claim asks for ρ_4(Ψ) = I over Z[t^{±1}]; this claim only gives congruences modulo fixed nonzero ideals, which each nontrivial Ψ fails for all but finitely many cyclotomic factors
artifacts:
  - research/artifacts/burau-cyclotomic-blindness-2026-09-17.md
  - experiments/burau-cyclotomic-blindness-2026-09-17/cyclotomic_blindness.py
  - experiments/burau-cyclotomic-blindness-2026-09-17/run.log
---

Let `ρ_4` be the unreduced Burau representation of `B_4` over `R = Z[t^{±1}]`, `Φ_q` the `q`-th cyclotomic
polynomial, `A_ij` the standard pure braid generators and `b = [A_14, [A_24, A_34]]`. Put `X_1 = σ_1^2`,
`X_2 = (σ_1σ_2)^6`, and `X_q = σ_1^{2j_q}` for `q ≥ 3`, with `j_q = q/2` for even `q` and `j_q = q` for odd `q`.

**Claim.** Let `g = Φ_{q_1} ⋯ Φ_{q_r}` (repetitions allowed). Put `Ψ_0 = b`, `Ψ_i = [X_{q_i}, Ψ_{i−1}]`, and
`Ψ_g = Ψ_r`. Then `Ψ_g` is a nontrivial Brunnian braid and `ρ_4(Ψ_g) ≡ I mod (t − 1)^2 g`.

Ingredients: `ρ_n(σ_1^{2j}) ≡ I mod (t^{2j} − 1)/Φ_2` and `ρ_n((σ_1σ_2)^{3j}) ≡ I mod (t^{3j} − 1)/Φ_3`;
`Brun_4 ⊆ [P_4, P_4] ⊆ G_4((t − 1)^2)`; commutators multiply congruence ideals; nontriviality from
pseudo-Anosov-ness of Brunnian braids and rigidity of twist powers.

Route: `brunnian-4-braids-meet-cyclotomic-burau-congruence-kernels-proof`.
