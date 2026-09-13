---
rg: 2
id: sp4-fd-unitary-reps-finite-image-via-superrigidity
kind: route
title: Margulis superrigidity with compact target forces finite image
target: sp4-fd-unitary-reps-have-finite-image
requires: []
---

A complete derivation of finite image for finite-dimensional unitary
representations of `Gamma = Sp_(2g)(Z)`, `g >= 2`, from Margulis
superrigidity (cited at statement level; see the claim's Trust surface).

Let `rho : Gamma -> U(k)`, `k < infinity`.

**Step 1 (compact image).**  `U(k)` is compact, so `rho(Gamma)` lies in a
compact group `K := U(k)`.

**Step 2 (superrigidity dichotomy).**  `G := Sp_(2g)(R)` is a connected
simple Lie group of real rank `g >= 2` and `Gamma <= G` is an irreducible
lattice.  Margulis superrigidity for homomorphisms of `Gamma` into compact
real Lie groups gives: either `rho(Gamma)` is finite, or there is a
finite-index subgroup `Lambda <= Gamma` and a continuous homomorphism
`R : G -> K` with `R|_Lambda = rho|_Lambda`.

**Step 3 (no continuous `G -> K`).**  Suppose `R : G -> K` is continuous.
Its differential `dR : sp(2g,R) -> k` is a homomorphism of Lie algebras.
`sp(2g,R)` is simple, so `ker(dR)` is `0` or all of `sp(2g,R)`.
- If `ker(dR) = 0`, then `dR` embeds `sp(2g,R)` as a subalgebra of the
  compact Lie algebra `k`.  The Killing form of a compact Lie algebra is
  negative semidefinite, and its restriction to any subalgebra is the
  Killing form of that subalgebra up to the ambient form's restriction;
  more directly, a subalgebra of a compact Lie algebra is compact
  (reductive with negative semidefinite Killing form).  But `sp(2g,R)` is a
  non-compact real form, with indefinite Killing form.  Contradiction.
- Hence `ker(dR) = sp(2g,R)`, i.e. `dR = 0`, so `R` is trivial on the
  identity component of `G`.  `G` is connected, so `R` is trivial.

**Step 4 (conclusion).**  In the second branch of Step 2, `R` trivial forces
`rho|_Lambda` trivial, so `Lambda <= ker rho` and `[Gamma : ker rho] <=
[Gamma : Lambda] < infinity`.  In the first branch `rho(Gamma)` is finite
outright.  Either way `rho(Gamma)` is finite and `rho` factors through the
finite quotient `Gamma / ker rho`.  QED.
