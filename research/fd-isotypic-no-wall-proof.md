---
rg: 2
id: fd-isotypic-no-wall-proof
kind: route
title: Match isotypic atoms by fiber size and mass, then refine to equality
target: fd-isotypic-part-of-a-kazhdan-image-carries-no-wall
requires: []
---

Notation as in the target. Write `Lambda_t = t Lambda t^(-1)` and
`alpha = Ad sigma(t)`, a trace-preserving automorphism of `M`.

**Step 0 (central projections from property (T)).** Every finite-dimensional
irreducible `rho` of a Kazhdan group is isolated in the dual (Wang, 1975): if
`pi` weakly contains `rho`, then `pi tensor rho-bar` weakly contains the
trivial representation, so by (T) it has invariant vectors, i.e. a nonzero
intertwiner `rho -> pi`. The closed point `ker rho` of `Prim C*(Lambda)` is
therefore open, and unitality gives a central projection `p_rho` with
`rho(p_rho) = 1` and `pi(p_rho) = 0` for every irreducible `pi` not equivalent
to `rho`. By local rigidity (`H^1(Lambda, ad rho) = 0`) and compactness of
`Hom(Lambda, U(n))`, there are finitely many such `rho` in each dimension. So
the `z_rho = sigma(p_rho)` are countably many pairwise orthogonal projections in
`sigma(Lambda)'' cap sigma(Lambda)'`, and `z_rho` projects onto the
`rho`-isotypic part of `sigma|Lambda`.

**Step 1 (`z` is invariant).** `t p_rho t^(-1)` is the central projection of the
irreducible `rho o Ad t^(-1)` of `Lambda_t`, so `alpha(z)` is the
finite-dimensional isotypic projection of `sigma|Lambda_t`. A
finite-dimensional `Lambda`-invariant subspace is `Lambda_t`-invariant and
finite-dimensional, so `z <= alpha(z)`. Both have the same trace and `tau` is
faithful, so `alpha(z) = z`.

**Step 2 (the two atomic algebras).** On `z`,
`B = sigma(Lambda)'' z = directSum_pi M_(delta_pi)(C) z_pi` has minimal central
projections `z_pi`, and `A = sigma(Lambda_t)'' z = alpha(B)` has minimal
central projections `z'_rho = alpha(z_rho)`. Here `A <= B`, and `alpha` matches
the multiset of pairs `(delta, tau(central projection))` of `B` with that of `A`.

**Step 3 (fiber sizes are monotone on joint pieces).** `z'_rho in A <= B` and
`z_pi` is central in `B`, so they commute. On a joint piece
`e = z_pi z'_rho != 0`, `A z'_rho z_pi` is a nonzero quotient of the factor
`M_(delta_rho)`, hence isomorphic to it, and it is a unital subalgebra of the
corner `e B e`, which is a matrix algebra `M_r` with `r <= delta_pi`. So
`delta_rho <= r <= delta_pi`.

**Step 4 (equal integrals force equality).** Let `f` be strictly increasing and
bounded on the positive integers. Summing over joint pieces,

```text
sum_e f(delta_rho) tau(e) = sum_rho f(delta_rho) tau(z'_rho)
                          = sum_pi f(delta_pi) tau(z_pi) = sum_e f(delta_pi) tau(e),
```

by Step 2, with every term of the difference nonnegative by Step 3. So
`delta_rho = delta_pi = r` on every piece of positive trace. Then `e` is the unit
of `B z_pi`, i.e. `z_pi <= z'_rho`: each central atom of `B` lies under a single
central atom of `A`.

**Step 5 (a refinement with the same mass multiset is trivial).** Within a fixed
fiber size, the atoms of `B` refine those of `A`, and the two families have the
same multiset of masses. Masses are summable, so each mass value occurs finitely
often. Let `m` be the largest mass. An atom of `B` of mass `m` lies under an
atom of `A` of mass at least `m`, hence exactly `m`, and equals it. Since both
families have equally many atoms of mass `m`, all of them coincide. Remove them
and descend; every atom is matched at a finite stage. So `z'_rho = z_pi` in
pairs, and on each `A z_pi` is a unital copy of `M_delta` inside `B z_pi ~= M_delta`,
hence equal. Therefore `A = B`.

**Step 6 (commutants).** `z` lies in `sigma(Lambda)'' cap sigma(Lambda)'` and
`y in zMz` commutes with `sigma(Lambda)` iff it commutes with `B`. The same holds
for `Lambda_t` with `A`. From `A = B`,
`(M cap sigma(Lambda)') z = (M cap sigma(Lambda_t)') z`. This is `(FIW1)`.
