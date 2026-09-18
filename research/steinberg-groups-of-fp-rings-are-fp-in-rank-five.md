---
rg: 2
id: steinberg-groups-of-fp-rings-are-fp-in-rank-five
kind: claim
title: For every finitely presented unital ring R and every n >= 5, the Steinberg group St_n(R) is finitely presented, with an explicit presentation
distinct_from:
  steinberg-finite-presentation-and-kazhdan-theorem: that is the rank >= 4 statement with property (T), whose finite-presentation part is imported from Krstic-McCool Theorem 3 without the primary text; this is the rank >= 5 case with a self-contained elementary proof and an explicit presentation, and says nothing about rank 4 or property (T).
  st-n-of-ring-quotient-adds-one-relator-per-ideal-generator: that is the quotient step from a free ring to R, one relator per ideal generator; this is finite presentation of St_n of the free ring, combined with that step.
artifacts:
  - research/artifacts/gq-referee-c-steinberg-finite-presentation-and-kazhdan-theorem.md
  - research/artifacts/gq-referee-a-steinberg-fp-rank-five-direct-proof.md
---

**ESTABLISHED** through `steinberg-groups-of-fp-rings-are-fp-in-rank-five-proof`. The proof is by
lane gq-referee-c (§2 and §4 of its artifact), with proof-gap review PASS by gq-referee-a. It is
elementary, and no novelty is claimed: the rank >= 4 statement is Krstic-McCool's Theorem 3.

**Statement.** Let `R = Z<g_1, ..., g_d | ρ_1, ..., ρ_l>` be a finitely presented unital ring and
let `n >= 5`. Then `St_n(R)` has the finite presentation described below.

**Generators.** `y_ij(u)` for `i ≠ j` in `[n]` and `u ∈ {1, g_1, ..., g_d}`.

**Relations.**
- (B1) `[y_ij(u), y_kl(v)] = 1` whenever `j ≠ k` and `i ≠ l`.
- (B2) For distinct `i, j, k`:
  - `[y_ij(1), y_jk(1)] = y_ik(1)`;
  - `[y_ij(g), y_jk(1)] = y_ik(g)`;
  - `[y_ij(1), y_jk(g)] = y_ik(g)`.
- One relator `φ(x_12(ρ_t))` for each `t`. It is obtained by writing each monomial of `ρ_t` as an
  iterated commutator of the generators. For example, `x_ij(ab) = [x_ik(a), x_kj(b)]` with
  `k ∉ {i, j}`.

**Use.** Every Steinberg-group route to `gl-n-q-explicit-natural-fp-overgroup` of rank at least 5
has a citation-free finite presentation. That includes `St_10(S)` of
`leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1` and `St_(6n+7)(R_L)`.

**Why rank 5.** Checking the commutation relations between two long root elements needs a free
index outside four given ones. At `n = 4`, the relations `[x_12(m), x_34(m')] = 1` need a separate
argument (gq-referee-c, §3). `St_3(R)` is not finitely presented whenever `R` surjects onto `F[t]`
for a field `F` (Krstic-McCool, Corollary 2, as quoted by Ershov–Jaikin-Zapirain).
