---
rg: 2
id: thompson-t-is-not-amenable-proof
kind: route
title: "T is not amenable: an invariant probability measure on the circle would conjugate T into the rotations"
target: thompson-t-is-not-amenable
requires: []
---

**Facts about T used.** (i) For every dyadic rational `θ`, the rotation
`R_θ(x) = x + θ` lies in T: it has slope 1, no breakpoints and maps dyadic
rationals to dyadic rationals. (ii) T is not abelian: `x_0 ∈ F ⊂ T` fixes `0` and
moves `1/2`, so `x_0 R_{1/2}(0) = x_0(1/2) ≠ 1/2 = R_{1/2} x_0(0)`.

**Proof.** Suppose T is amenable. T acts on the compact metrizable space `S^1`
by homeomorphisms, so it preserves a Borel probability measure `μ` (an amenable
discrete group fixes a point in every nonempty compact convex set on which it
acts continuously and affinely; apply this to the weak-* compact convex set of
probability measures on `S^1`).

*Step 1: `μ` has no atoms.* If it had atoms, let `m` be the largest atomic mass;
it exists because only finitely many atoms have mass at least any given positive
number. The set of atoms of mass `m` is finite, nonempty and T-invariant. But the
T-orbit of any point `x` contains `x + θ` for every dyadic `θ`, an infinite set.
Contradiction.

*Step 2: `μ` has full support.* The support of `μ` is closed, nonempty and
T-invariant, so it contains a full orbit, which is dense by (i). Hence the support
is `S^1`.

*Step 3: conjugation to rotations.* For points `a, b` of the circle write `[a,b)`
for the positively oriented half-open arc. Define `h: S^1 -> R/Z` by
`h(x) = μ([0,x)) mod 1`. By Steps 1 and 2, `h` is continuous, strictly increasing
on the arc and of degree one, so it is a homeomorphism. Arc measures add modulo 1:
`μ([a,b)) + μ([b,c)) ≡ μ([a,c)) mod 1`. For `g ∈ T`, `g` is orientation preserving,
so `g([0,x)) = [g(0), g(x))`, and invariance gives `μ([g(0), g(x))) = μ([0,x))`.
Therefore

```text
h(g(x)) ≡ μ([0, g(0))) + μ([g(0), g(x))) = h(g(0)) + h(x)   (mod 1),
```

so `h g h^{-1}` is the rotation by `h(g(0))`. The map `g ↦ h g h^{-1}` is an
injective homomorphism from T to the abelian group of rotations, so T is abelian,
contradicting (ii). Hence T is not amenable. ∎

(T also contains non-abelian free subgroups, for instance through Thurston's
piecewise-projective model containing `PSL_2(Z)`; that route is not needed here.)
