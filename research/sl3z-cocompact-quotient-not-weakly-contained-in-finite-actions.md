---
rg: 2
id: sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions
kind: claim
title: For Λ from a cubic division algebra, SL3(Z) on SL3(R)/Λ is not weakly contained in finite actions
distinct_from:
  sl3z-cocompact-quotient-uniformly-far-from-finite-actions: that excludes finite actions whose marks are good at every vertex; this asks for a uniform positive proportion of bad vertices, i.e. the exclusion of weak containment
  sl3z-cocompact-quotient-admits-no-topological-microstates: that is nonsoficity, allowing almost-actions; this allows only honest finite actions, with a vanishing proportion of defects
---

**OPEN (two-sided).** Let `Λ <= SL_3(R)` satisfy hypothesis (R) of
`sl3z-cocompact-quotient-uniformly-far-from-finite-actions` (for instance `Λ <= SL_1(D)(Q)` with `D` a
cubic division algebra). There are `ε_0, θ_0 > 0` such that for every finite `SL_3(Z)`-set `V` and every
`y : V → SL_3(R)/Λ`, at least a proportion `θ_0` of the pairs `(v, s)`, `s ∈ {e_ij^(±1)}`, have
`d̄(y(sv), s·y(v)) >= ε_0`.

**Equivalent forms.**
1. `SL_3(Z) ↷ (SL_3(R)/Λ, Haar)` is not weakly contained in finite `SL_3(Z)`-actions. Partition statistics
   of a finite action give marks with few bad pairs, as in part 1 of
   `uniquely-ergodic-action-sofic-iff-topological-microstates`. Conversely, marks with few bad pairs
   equidistribute by unique ergodicity and reproduce the statistics, as in part 2.
2. `SL_3(R)/Λ` is not a factor of a Loeb ultraproduct of finite `SL_3(Z)`-actions.

**Contrast (sharp line).**
* Weakly contained in finite actions: `SL_3(R)/SL_3(Z)` (Hecke orbits), `T^3` (torsion points), and
  Bernoulli shifts (random colourings of large-girth congruence quotients).
* Here: the proportion-zero case is `sl3z-cocompact-quotient-uniformly-far-from-finite-actions`.

**Why it matters.** Together with stability of `SL_3(Z)` in finite actions it gives nonsoficity
(route `sl3z-cocompact-nonsofic-from-stability-and-no-finite-approx`). It would also be a
dynamical detector of commensurability: soficity by exact finite models holds exactly for lattices in
the class of `SL_3(Z)`. Conversely, if this claim fails, the finite actions with sparse bad pairs are
already microstates: an honest action has no multiplication defect. So `SL_3(Z) ↷ SL_3(R)/Λ` would be
sofic by part 2 of `uniquely-ergodic-action-sofic-iff-topological-microstates`. The claim is therefore
two-sided for the problem itself. A disproof settles soficity, and a proof reduces nonsoficity to
stability of `SL_3(Z)` in finite actions.

## Attempts

* **Holonomy with defects.** On an honest action with bad pairs, the `Λ`-labels
  (`sl3z-cocompact-microstates-carry-flat-lambda-labels`) are flat only on relator cells avoiding the
  defects. The labelled system is an action of the free group, with unconstrained holonomy around
  defect cells. Norm drift needs a finite invariant labelled region, which exists only when the
  holonomy is finite. Dies at: rounding a `Λ`-valued almost-cocycle over a finite action to an exact one
  in Hamming distance, with bounded labels. That is a cosystolic-expansion statement with nonabelian
  coefficients, not a property (T) statement.
* **Closing along loops.** Along a defect-free loop the label product is forced by the marks. Dies at:
  loops of an expanding finite action have length `>= girth ~ log|V|`, a defect proportion `δ` meets a
  loop with probability about `δ log|V|`, and the accumulated metric error along a loop grows like the
  norm of its partial products, so defect-free loops constrain nothing.
* **Self-joinings.** Right translations `R_κ` of a congruence quotient `SL_3(Z/N)` commute with the action,
  so `(y, y∘R_κ)` pushes forward to an almost-invariant self-joining. In the Loeb limit, ergodicity makes
  each `κ` have a pure type, among the diagonal, Hecke-correspondence and other joinings; the classification
  of invariant measures of the diagonal on `(SL_3(R)/Λ)^2` would need Benoist--Quint II (not imported).
  Dies at: averaging over `κ` gives the independent joining, and nothing forces a large subgroup of
  diagonal type.
* **Kazhdan projections.** Build an almost-invariant vector in `ℓ^2(V) ⊗ L^2(SL_3(R)/Λ)` from bumps at the
  marks, and use that invariant vectors are constants. Dies at: left translations distort bumps by
  `Ad(s)`, which has no invariant shapes, so the vector is never almost invariant.
* **Koopman representation (ex2-sl3z-cocompact-weak-containment; recalled, not imported).** Weak containment
  would put `L^2_0(SL_3(R)/Λ)|_Γ` inside the closure of the finite-image representations. Take `D` of
  prime degree `3`. By Jacquet--Langlands every irreducible constituent `π` of `L^2_0(SL_3(R)/Λ)` is the
  archimedean part of a cuspidal representation of `GL_3`, so `π` occurs in `L^2(SL_3(R)/Γ(N))` for some
  `N`. `Γ ↷ SL_3(R)/Γ(N)` has infinitely many finite orbits, and they equidistribute
  (`hecke-orbits-make-lattice-quotient-actions-sofic`). That action is weakly contained in finite
  actions, hence so is its Koopman representation, and with it `π|_Γ`. Dies at: the action is spectrally
  invisible, so any obstruction must be non-spectral. In particular, the route through property FD
  cannot detect it. That route uses MD ⇒ FD, item (6) of Section 5 in Burton--Kechris, arXiv:1611.07921,
  read from the PDF. The survey also lists as open whether MD ⇒ ¬(T).
* **Separable models (proved; ex2-sl3z-cocompact-weak-containment).** Popa product superrigidity followed
  by Ioana profinite superrigidity shows that `SL_3(R)/Λ` is not a factor of Bernoulli times any free
  ergodic profinite action (`sl3z-cocompact-not-factor-of-bernoulli-times-profinite`). Dies at: the same
  argument, with superrigidity and Borel density, also excludes the Hecke action on
  `SL_3(R)/SL_3(Z)`, which *is* weakly contained. So the question lives only in ultraproducts.
* **Rounding route (conditional; ex2-sl3z-cocompact-weak-containment).** The first Attempt's missing
  ingredient is posed as the marks-free open claim `sl3z-lambda-almost-cocycles-round-to-flat-ones`.
  Its conclusion is weakened to a vanishing Hamming distance plus a vanishing log-norm budget on the
  repaired labels. Route `sl3z-cocompact-exclusion-from-almost-cocycle-rounding` proves that it implies
  this claim: flat labels have finite holonomy, and norm drift on the resulting finite orbits prices the
  repairs. Measurable limits cannot supply the rounding, since Zimmer superrigidity permits the identity
  homomorphism (see that claim's Attempts).
