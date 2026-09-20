---
rg: 2
id: fpbs-finite-fibre-bb-classes-are-boundary-squares
kind: claim
title: For a nonelementary hyperbolic group, an ergodic imp action over a boundary class has fibres that are a.e. finite or a.e. infinite; in the finite case the class contains a Gamma-invariant sigma-finite boundary measure lambda that is infinite on every open set, the crossing diagonal is conservative exactly when lambda x lambda is, and a conservative square lambda x lambda already gives fixed price one, so finite-fibre Bevilacqua--Bowen certificates are exactly conservative squares of invariant boundary measures, which are never Radon currents
distinct_from:
  fpbs-finite-measure-ray-codes-die-on-rank-one-lattices: that kills every class C for which C x C carries an invariant Radon current (Corollary 5) and names Radon-free crossing classes. This answers its first test for finite-fibre actions. A conservative crossing diagonal does force a sigma-finite invariant measure in C x C, namely lambda x lambda, but that measure is never Radon, so its flow-entropy argument cannot be extended to this case.
  fpbs-dini-boundary-class-diagonal-dissipative: that bounds returns by shadow sums and kills Dini-dominated classes. This reduces the finite-fibre case to one boundary action, (dGamma, lambda) with lambda invariant, to which the Dini filter still applies, and shows that a survivor is itself a certificate.
  fpbs-hyperbolic-bb-criterion-obstruction: that forces a point boundary map and rules out boundary-pair factors. This classifies imp actions over a fixed boundary class by fibre mass and proves an exact two-way reduction for the finite-mass half.
---

**ESTABLISHED (written proof: `research/fpbs-finite-fibre-bb-classes-are-boundary-squares-proof.md`).** The proof
uses uniqueness of disintegration, the recurrence form of conservativity, minimality of `Gamma` on `dGamma`, the
Harrington--Kechris--Louveau form of the Glimm--Effros dichotomy, Adams' boundary amenability theorem, and the
Bevilacqua--Bowen criterion as recorded in `fpbs-hyperbolic-bb-criterion-obstruction`.

**Why this matters for the flagship.** For a cocompact `Sp(n,1)` lattice (property (T), fixed price open), the
Bevilacqua--Bowen (BB) route needs an amenable ergodic PDR imp action `Z` with a boundary map `xi : Z -> dGamma`.
`fpbs-finite-measure-ray-codes-die-on-rank-one-lattices` (Corollary 5) showed that the boundary class `C` of a
certificate cannot have `C x C` equivalent to an invariant Radon current. It asked whether a conservative crossing
diagonal forces a sigma-finite invariant measure in `C x C`, and whether that measure must be Radon. This node
settles both questions for every imp action whose fibres over `dGamma` have finite mass. It also shows that this half
of the BB route is a statement about one boundary action: it is equivalent to the problem below.

**The object changes.** Earlier filters looked at the size of `C` (Dini), at codes (ray codes), or at currents
(Radon measures on `d^2 Gamma`). Here the object is the **fibre mass** of `Z` over `dGamma`, and the certificate
problem becomes a statement about one invariant, non-Radon measure on the boundary.

## Setting

`Gamma` is a nonelementary hyperbolic group, `(Z, mu)` is an ergodic imp `Gamma`-space, and `xi : Z -> dGamma` is
measurable and equivariant. `lambda_0` is a probability measure in the class `C = [xi_* mu]`, and
`mu = ∫ mu_x d lambda_0(x)` is the disintegration, with `mu_x` sigma-finite on `xi^{-1}(x)`. The **crossing
diagonal** is `W = {(z,z') : xi(z) != xi(z')}` with `mu x mu`. Conservativity means no wandering set of positive
measure, or equivalently, that a.e. point of each positive-measure set returns to it infinitely often.

## Results

**Theorem 1 (fibre dichotomy).** Either `mu_x` is finite for `lambda_0`-a.e. `x`, or `mu_x` is infinite for
`lambda_0`-a.e. `x`.

**Theorem 2 (finite fibres: an invariant boundary measure, never Radon).** Suppose the fibres are finite, and put
`h(x) = mu_x(Z)`. Then `lambda = h lambda_0` is a `Gamma`-invariant, sigma-finite, ergodic, nonatomic measure in `C`.
Moreover:
1. `lambda(U) = infinity` for every nonempty open `U ⊂ dGamma`. So `lambda x lambda` is a sigma-finite invariant
   measure in the class of `C x C`, and it gives infinite mass to every product `U x V` of nonempty open sets. It is
   Radon nowhere on `d^2 Gamma`, and its flow measure on `Gamma \ (d^2 Gamma x R)` is infinite on every open set.
2. `Gamma` acts conservatively on `W` if and only if it acts conservatively on `(d^2 Gamma, lambda x lambda)`. More
   precisely, `Con(W)` is the preimage of `Con(d^2 Gamma, lambda x lambda)` up to null sets.

**Theorem 3 (a conservative square is a certificate).** Let `lambda` be any ergodic, nonatomic, sigma-finite,
`Gamma`-invariant measure on `dGamma`. If `Gamma` acts conservatively on `(dGamma x dGamma, lambda x lambda)`, then
`(dGamma, lambda)` is an amenable, ergodic, PDR imp action with infinite non-atomic ergodic components, so, by the
Bevilacqua--Bowen criterion, `Gamma` has fixed price one.

**Corollary 4 (exact reduction of the finite-fibre half).** For a nonelementary hyperbolic group the following are
equivalent:
1. some ergodic imp `Gamma`-space with a boundary map and a.e. finite fibres has a conservative crossing diagonal;
2. some ergodic, nonatomic, sigma-finite, `Gamma`-invariant measure on `dGamma` has a conservative square.
Both directions are proved (1 => 2 by Theorem 2, 2 => 1 by taking `Z = (dGamma, lambda)`). In particular any
finite-fibre BB certificate can be replaced by the boundary action `(dGamma, lambda)` itself.

**Proposition 5 (the class is not empty).** Every nonelementary hyperbolic group carries ergodic, nonatomic,
sigma-finite, infinite `Gamma`-invariant measures on `dGamma` (by Glimm--Effros). The open question is only whether
the square of one of them can be conservative.

**Corollary 6 (filters and calibration).**
1. *Dini.* If `lambda` has a conservative square, then its class is singular to every finite Dini measure
   (Theorem B and Theorem C of `fpbs-dini-boundary-class-diagonal-dissipative`, applied to `Z = (dGamma, lambda)`). So
   every finite restriction of `lambda` has lower local dimension `0` almost everywhere.
2. *Cost larger than one.* If `Gamma` has a free pmp action of cost `> 1` (free groups `F_r`, `r >= 2`, surface
   groups, any `Gamma` with `beta_1^(2)(Gamma) > 0`), then **no** invariant sigma-finite ergodic nonatomic measure on
   `dGamma` has a conservative square. This follows from Theorem 3. It is a dynamical statement about boundary
   actions obtained from cost theory.
3. *Radon currents cannot see this case.* By Theorem 2.1 the measure forced in `C x C` is never Radon. So the entropy
   argument of `fpbs-finite-measure-ray-codes-die-on-rank-one-lattices` does not apply, and this is exactly why.

## What this leaves (named open statements)

- **(II_inf-square) Invariant boundary squares.** For a cocompact lattice `Gamma < Sp(n,1)`, is there an ergodic,
  nonatomic, sigma-finite, `Gamma`-invariant measure `lambda` on `S^{4n-1} = dGamma` such that `Gamma` acts
  conservatively on `(S^{4n-1} x S^{4n-1}, lambda x lambda)`? "Yes" gives fixed price one for `Gamma` (Theorem 3).
  "No", together with the infinite-fibre case below, closes the BB route on `Gamma`. The first test: whether an
  invariant `lambda` can have finite restrictions whose shadow-product sums diverge (the Dini count is the only known
  obstruction, and invariance has not yet been used in it).
- **Infinite fibres.** When the fibres are infinite (for example Maharam extensions of type III classes), whether a
  conservative crossing diagonal forces a sigma-finite invariant measure in `C x C` remains open.

## Attempts

- **fp-audit (2026-09-19), calibration lane: an attempt to refute this node. It survives, and one clause is
  corrected.**
  - **Checked against the Bevilacqua--Bowen TeX source** (arXiv:2510.05459):
    - the verbatim PDR definition;
    - amenable implies limit-amenable with normalized cost 1;
    - the proof chain of Theorem 8.1: ergodic component, then Bernoulli product, then Poisson suspension.
  - **Checked in this node's proof:** the cocycle formula, Steps 2 and 3 in both directions, and Proposition 5.
  - **The gap.** Theorem 2 says `lambda` is nonatomic, but the Setting does not assume that `C` is nonatomic. For an
    atomic `C`, `lambda` is `c` times counting measure on one orbit.
  - **Why Corollary 4 and Theorem 3 stand.** An atomic finite-fibre class always has an infinite dissipative part in
    its square, so it never gives a conservative crossing diagonal.
  - **Calibration.** `Gamma = (Z/2 * Z/2) * Z` acting on `Gamma / <st>` has cost `> 1`. The conservative part of its
    square is nonzero but not conull, and the action is not PDR. So the nonatomic hypothesis of Theorem 3 is needed.
  - Recorded in `fpbs-finite-fibre-boundary-squares-atomic-class-audit` and its proof. No `invalidates:` claim.
