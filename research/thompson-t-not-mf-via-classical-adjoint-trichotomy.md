---
rg: 2
id: thompson-t-not-mf-via-classical-adjoint-trichotomy
kind: route
title: Push every small-defect Z/4 * Z/3 pair onto one invariant simple ideal, land densely in a classical adjoint group, and gap the three classical families separately, bypassing the rounding condition (S_T)
target: thompson-t-has-full-mf-radical
requires: [thompson-t-witnesses-are-dense-in-simple-adjoint-groups, thompson-t-gap-on-dense-projective-unitary-images, thompson-t-gap-on-dense-orthogonal-adjoint-images, thompson-t-gap-on-dense-symplectic-adjoint-images, thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes]
---

*Distinct from* `thompson-t-not-mf-via-triangle-cover-rounding`, which splits the target into (R_Delta)
and the rounding condition (S_T). This route never passes through `Delta` or rounding. It is the
`T`-analogue of `thompson-v-not-mf-via-classical-adjoint-trichotomy`.


**The route.**
- Let `eps` be the minimum of the constants of the three level-T gap claims.
- Suppose `T` were MF. By `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`, there are nontrivial
  irreducible pairs `sigma_n` with `D(sigma_n) -> 0`.
- By item 1 of `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`, which is the corollary of
  `lie-closure-trichotomy-without-finite-quotients`, some `Gap_T(X)` fails. Concretely, for large `n`
  there is a dense `tau_n : Z/4 * Z/3 -> Inn(X(k))`, with `k` large, and
  `D(tau_n) <= 2 D(sigma_n) < eps`.
- This contradicts `Gap_T(X)`. Hence `T` is not MF, that is, `T` has full MF radical.

**Each hole is necessary.** By item 1 of the parent claim, the target implies each of the three gaps.
So the route loses nothing: it is an exact reformulation.

**What changed.** Compared with `thompson-t-not-mf-via-triangle-cover-rounding`, there is no stability
statement (S_T), no doubling `phi (+) phi-bar`, and no padding. The whole target is now three uniform
lower bounds, each about dense homomorphisms of a virtually free group into one classical compact
adjoint family. Each bound can be refuted on its own, by an explicit sequence of dense homomorphisms.
