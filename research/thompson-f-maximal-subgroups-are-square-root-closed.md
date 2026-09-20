---
rg: 2
id: thompson-f-maximal-subgroups-are-square-root-closed
kind: claim
title: Every maximal subgroup of infinite index in Thompson's group F is closed under square roots, that is, x^2 in H forces x in H
distinct_from:
  thompson-f-has-no-faithful-2-transitive-action: that is the negative answer to Problem 2.20, which asks about one orbital of one maximal subgroup; this asks every maximal subgroup of infinite index to have no self-paired non-diagonal orbital at all, which is strictly stronger
  jones-subgroup-coset-spaces-carry-invariant-orders: that proves the stronger relative-convexity property for the known Jones-type maximal subgroups; this conjectures the weaker square-root property for all maximal subgroups of infinite index
  thompson-f-two-transitive-stabilizers-are-piecewise-closed: that is a closure property of a 2-transitive point stabilizer under piecewise gluing; this is closure under square roots, a property that every 2-transitive point stabilizer must fail
---

**OPEN (conjecture).** Let `H < F` be a maximal subgroup of infinite index. If `x ∈ F` and
`x² ∈ H`, then `x ∈ H`.

**Equivalent form.** For a subgroup `H` of a group `G` the following are equivalent:
- some non-diagonal orbital of `G` on `G/H` is self-paired;
- some `x ∉ H` has `x² ∈ H`.

Proof. If `x` swaps `H` and `xH`, then `x²H = H`. Conversely, `x ∉ H` with `x² ∈ H` swaps `H` and
`xH`. So the conjecture says that `F` acting on `F/H` has only non-self-paired non-diagonal
orbitals, for every maximal `H` of infinite index.

**Stronger form.** Every maximal subgroup of infinite index is relatively convex: `F/H` carries an
`F`-invariant total order. This implies square-root closure, because `H ≺ xH` forces
`xH ≺ x²H`, hence `H ≺ x²H`.

**Evidence.** The stronger form holds for every explicitly described maximal subgroup of infinite
index:
- the parabolic subgroups `Stab(α)`;
- the Golan–Sapir subgroup `Ψ^{-1}(\vec F)`;
- Golan's subgroups `ν(\vec F_p)`.

See `jones-subgroup-coset-spaces-carry-invariant-orders`.

**Why it matters.** It implies the negative answer to Problem 2.20, by route
`thompson-f-no-two-transitive-via-square-root-closure`. It is not formally
weaker than that answer. It is, however, a statement about subgroups rather than actions, and it
can be tested against any new maximal subgroup by exhibiting a single `x`.

**Test for a refutation.** Find a maximal subgroup `H` of infinite index, for instance one of
Golan's maximal subgroups with `n` orbits on the dyadics, or one produced by Zorn's lemma above a
finitely generated `H_0` with `H_0[F,F] = F`, together with some `x ∉ H` such that `x² ∈ H`.
Such an `H` would not settle Problem 2.20, but it would kill this route.

Note: `H[F,F] = F` for every maximal `H` of infinite index, since `H ⊇ [F,F]` would force finite
index. So the abelianization `ℤ²` gives no obstruction to square roots. In `F_{1,2}`, which has
index 2, every square lies in the subgroup. So the finite-index hypothesis is needed.
