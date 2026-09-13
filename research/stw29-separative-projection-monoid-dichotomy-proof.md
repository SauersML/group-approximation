---
rg: 2
id: stw29-separative-projection-monoid-dichotomy-proof
kind: route
title: A finite and an infinite projection give the separativity failure x = u, y = u + r, and separativity survives inductive limits
target: stw29-separative-projection-monoid-dichotomy
requires: [ara-goodearl-tame-refinement-monoids-separative]
---

`V(A)` is conical and, for simple `A`, simple: every nonzero class is an order
unit.  Facts (F1) and (F2) are as in `stw29-counterexample-level-two-fingerprint-proof`.
(F1): anything above an infinite element is infinite.  (F2): in a simple
conical monoid, infinite elements are properly infinite.

**Part 1.**  Let `q` be a nonzero finite projection and `p` an infinite
projection in some `M_k(A)`.  Simplicity gives `[p] <= l[q]`, so `l[q]` is
infinite by (F1).  Let `n >= 2` be least with `n[q]` infinite, and put
`u = (n-1)[q]`, which is finite.  Then `2u >= n[q]` is infinite by (F1),
hence properly infinite by (F2).  Write `2u = 4u + w` and `r = 2u + w`.  Then
`2u + r = 2u`, and with `x = u`, `y = u + r`,

```text
x + y = 2u + r = 2u = 2x,        2y = (2u + r) + r = 2u.
```

If `x = y`, then `u = u + r` with `r != 0` (conicality), so `u` is infinite, a
contradiction.  So `V(A)` is not separative.

**Part 2.**  Suppose `A` has (SP) and `V(A)` is separative.  If no matrix
algebra over `A` has an infinite projection, `A` is stably finite.  Otherwise
part 1 shows that every nonzero projection of `A` is infinite.  By (SP) every
nonzero hereditary subalgebra contains a nonzero projection, hence an infinite
one, and for simple algebras this is pure infiniteness.  Real rank zero implies
(SP).

Weak cancellation for simple `A`: whenever `p direct_sum r ~ q direct_sum r`
with `p, q` nonzero (all nonzero projections are full), then `p ~ q`.  If this
holds and `2x = 2y = x + y`, then either `x = 0 = y` (conicality) or
`x + x = y + x` with `x, y != 0`, which gives `x = y`.  Conversely, in a simple
conical monoid separativity is equivalent to cancellation
`a + c = b + c`, `c <= ma`, `c <= mb` implies `a = b` (Ara--Goodearl--O'Meara--
Pardo 1998, Lemma 2.1).  The side conditions are automatic for nonzero `a, b`,
which is weak cancellation.

**Tame case.**  Tame refinement monoids are separative
(`ara-goodearl-tame-refinement-monoids-separative`, Theorem 2.3).  The listed
classes are tame by Examples 2.2 and Theorem 3.1 there.

**Inductive limits.**  `V` is continuous: `V(lim A_n) = lim V(A_n)`.  Every
projection in the limit is equivalent to the image of a projection at a finite
stage, and equivalences between images are realized at a later finite stage
after perturbation.  Separativity is a Horn implication among finitely many
equations, so it passes to inductive limits of monoids.  Represent `x`, `y` at
stage `n`, push the three equalities to a stage `m` where they hold, apply
separativity of `V(A_m)`, and push back.

**Building blocks.**
* Stable rank one gives cancellation of projections (Rordam, Acta 2003,
  page 29), hence separativity.
* In a purely infinite simple `B`, every nonzero projection is properly
  infinite, and two properly infinite full projections are equivalent iff they
  have the same `K_0` class (Cuntz).  So `V(B) \ {0}` embeds in the group
  `K_0(B)`.  If `2x = 2y = x + y` and `x != 0`, then `y != 0`, and group
  cancellation gives `x = y`.  If `x = 0`, then `y = 0`.
* `C(X) tensor O_infinity` is purely infinite (Kirchberg--Rordam), so every
  nonzero projection is properly infinite.  For connected `X` a nonzero
  projection is nonzero at every point, hence full, and the Cuntz argument
  applies.
* `V` of a finite direct sum is the product monoid.
* If only finitely many stages fail separativity, discard them; the limit is
  unchanged.

**Rordam's blocks.**  `B = lim M(C(Z, K))` (Rordam, Acta 2003, Section 5) is
simple and contains a nonzero finite and an infinite projection.  By part 1,
`V(B)` is not separative, so cofinally many (all, by stationarity) building
blocks have non-separative `V`.
