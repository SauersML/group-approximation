---
rg: 2
id: twisted-rank-models-kill-visible-cyclic-corner-witnesses
kind: claim
title: A rank model with a nonzero visible scalar component rules out cyclic corner witnesses on every twisted Leavitt host
distinct_from:
  anti-central-rank-models-kill-ternary-corner-witnesses: that is the host q = 3 with the swap w and d = s0 t0 − s1 t1; this is every host with m dividing q − 1, including the characteristic-two host (4, 2, 3), and specializes to that claim at (3, 2, 2).
  leavitt-visible-colimit-factors-admit-k0-states: that is the open assertion that the colimit visible factor has a state; this produces a state on the subgroup algebra from any rank model whose visible scalar component is nonzero.
artifacts:
  - research/artifacts/quaternary-twisted-corner-census-2026-09-12.md
---

**ESTABLISHED** (independently re-derived by lane `w3-vf-linear`: Section 2 of
`research/artifacts/w3-vf-linear-verification-2026-09-12.md`, commit 2e937868ed). Let `q = p^r`, `d >= 2`, and `m >= 2` admissible with `p ∤ m` and `m | q − 1`. Let `g`
be the `m`-cycle permutation unit of an `m`-ary Leavitt family in `L_(F_q)(1,d)`, `δ = Σ_i ζ^i s_i t_i`
with `ζ` of order `m`, and `e_1 = eps_iota (1/m) Σ_k [g^k]`, where `eps_iota` is the idempotent of the
inclusion character of the scalars `Z = F_q^x`. Let `Γ` contain `Z`, `g` and `δ`, and put
`S_Γ = eps_iota F_q[Γ]`.

Suppose `σ : Γ -> M^x` is a homomorphism into an `F_q`-algebra with a Sylvester matrix rank function
that is positive on nonzero idempotents, and `σbar(eps_iota) != 0` for its linear extension. Then
`(K_0(S_Γ), [eps_iota])` has a state, and no `b', c'` in `S_Γ` satisfy `c' e_1 b' = eps_iota`.

Why: the `m` isotypic idempotents of `⟨g⟩` are orthogonal, sum to `eps_iota` and are conjugate by
powers of `δ`, so `r(σbar(eps_iota)) = m · r(σbar(e_1))`, while a witness forces
`r(σbar(eps_iota)) <= r(σbar(e_1))`.

**Support filter.** A witness makes every such `σ` on `⟨Z, g, δ, supp b', supp c'⟩` kill `eps_iota`. In
particular no finite-dimensional representation of that subgroup has a vector on which each scalar
acts by itself.

Proof: Section 2 of the artifact, route `twisted-rank-models-kill-cyclic-corner-proof`.
