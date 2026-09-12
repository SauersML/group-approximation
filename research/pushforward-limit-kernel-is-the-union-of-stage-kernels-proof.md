---
rg: 2
id: pushforward-limit-kernel-is-the-union-of-stage-kernels-proof
kind: route
title: A fibre-sum formula, then separate the support at a finite stage
target: pushforward-limit-kernel-is-the-union-of-stage-kernels
requires: []
artifacts:
  - GroupApproximation/Algebra/AbelianLampPushforward.lean
  - GroupApproximation/Algebra/AbelianLampTelescopeKernel.lean
---

## Why sufficient

Machine-checked, no `sorry`, no axiom, no literature premise.

**The pushforward.**  `AbLamp A X := Multiplicative (X →₀ A)` is the abelian lamp
group over a site set, written multiplicatively; `push q` is
`Finsupp.mapDomain q` promoted to a monoid homomorphism of multiplicative lamp
groups (`AddMonoidHom.toMultiplicative`), with `toAdd_push` the definitional
bridge.  `push_comp` is functoriality, and `ker_le_ker_comp` is the resulting
monotonicity of kernels — the statement Theorem 37.5 needs before taking a union.
`push_comm_of_equivariant` is the commutation with coordinate permutations, and
`push_single_mul_single_inv` is the same-fibre-difference generator computation.

**The fibre-sum formula.**  `mapDomain_apply_eq_sum`: the value of a pushforward
at a target site `b` is the sum of the source values over
`v.support.filter (fun x => q x = b)`.  Proved by unfolding `mapDomain` as a
`Finsupp.sum` of singles and applying `Finset.sum_filter`.  This is the whole
mechanism: it makes both sides of the union step computations over the same
finite support.

**The union step.**  `ker_push_eq_iSup`, by `le_antisymm`.

- `⊇`: each `ker (push (q n))` sits inside `ker (push q_inf)` by the
  factorization `q_inf = p ∘ q n` and functoriality, so the supremum does too.
- `⊆`: given `f` in the limit kernel, apply the separation hypothesis to the
  finite set `v.support`, where `v = toAdd f`.  At the resulting stage `n` the
  fibres of `q n` and `q_inf` cut the support identically, so the fibre-sum
  formula gives the same value at every site, which is `0`.  Hence `f` is in
  `ker (push (q n))`, one of the members of the supremum.

## Scope

`A` is an arbitrary additive abelian group and the site sets are arbitrary types;
no finiteness, countability, or torsion hypothesis appears.  The separation
hypothesis is stated for `Finset X`, which is exactly the strength the `Finsupp`
support provides — weakening it to "every element" would be false, and
strengthening it to "every subset" would be unusable.
