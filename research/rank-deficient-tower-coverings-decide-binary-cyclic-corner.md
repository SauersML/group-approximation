---
rg: 2
id: rank-deficient-tower-coverings-decide-binary-cyclic-corner
kind: claim
title: Fewer than 3^k conjugate tower ideals summing to the whole binary group algebra make the cyclic corner full
distinct_from:
  binary-cyclic-corner-full-iff-complement-corner-has-no-state: that is Theorem B, the equivalence of fullness with the absence of states on the complement corner; this is a sufficient finite certificate that is linear once the left factors are fixed, derived from Theorem B and the one-value gap.
  binary-cyclic-averaging-idempotent-is-full-on-leavitt-units: that is the open fullness target over the Leavitt units; this reformulates what a witness may look like, and decides nothing about whether one exists.
  thompson-v-order-three-averaging-idempotent-is-full: that is the open target over Thompson's V; this certificate form applies to V as a Theorem B host but is not a solution.
artifacts:
  - research/artifacts/gk3-binary-fullness-2026-09-14.md
---

**ESTABLISHED** by `rank-deficient-tower-coverings-decide-corner-proof` (lane gk3-binary-fullness, 2026-09-14;
not independently re-derived yet).

**Setting.** Let `Γ` be a host of Theorem B (`binary-cyclic-corner-full-iff-complement-corner-has-no-state`): a
`D`-stable subgroup of the units of `L_(F_2)(1,2)` containing `g` and the nine-cylinder permutation units `π_M`.
Examples are the whole unit group and Thompson's `V`. The proof uses only Theorem B, the halving map `ψ'` and the
tower relations, so it also covers `2V` to the extent that Theorem B holds there (artifact Section 1.4). Put
`A = F_2[Γ]`, `e = 1 + [g] + [g²]`, and `E_k = Σ_(h in C_3^k) [h]` with `C_3^k = ⟨g, D(g), ..., D^(k-1)(g)⟩`,
so `E_1 = e`.

**Statement.** The following are equivalent.
1. `c e b = 1` is solvable in `A`.
2. For some `k >= 1` and some `r < 3^k` there are `a_1, ..., a_r` and `b_1, ..., b_r` in `A` with
   `a_1 E_k b_1 + ... + a_r E_k b_r = 1`.

**Coset form.** When the left factors are group elements `x_j` in `Γ`, statement 2 says: the indicator `δ_1` of
the identity is a sum over `F_2` of `r` finitely supported functions `f_j : Γ -> F_2`, where `f_j` is invariant
under left translation by the conjugate `K_j = x_j C_3^k x_j^(-1)`. The right ideal `E^(K_j) A` is exactly this
space of functions. For fixed left factors, statement 2 is a linear system over `F_2`, and an infeasible
bounded instance has a checkable dual certificate.

**Why it matters.**
- It turns the bilinear equation `c e b = 1` into linear searches: fix `r < 3^k` left factors, solve for the `b_j`.
- The bound `r < 3^k` is what carries the content. Coverings with `r > 3^k` already occur in finite groups: in
  `F_2[C_3²]` the four order-three subgroups `K` give `δ_1 = 1_(C_3²) + Σ_K 1_K`, with `r = 4` at `k = 1`
  (artifact Section 2).
- A coset certificate restricts to `L = ⟨K_1, ..., K_r⟩`, so `L` must be nonsofic: the rank function of a sofic
  approximation gives each `E^(K_j)` rank `3^(-k)`, and `r · 3^(-k) < 1`.
- `two-order-three-coset-ideals-never-contain-one` kills the coset form at `k = 1`, so a coset certificate needs
  `k >= 2`. At `k = 1` only left factors outside the group remain.

## Attempts

Established, not open. Artifact Sections 2–4 record the proof, the small-support census design and where it stops.
