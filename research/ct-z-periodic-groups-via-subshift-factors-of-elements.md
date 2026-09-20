---
rg: 2
id: ct-z-periodic-groups-via-subshift-factors-of-elements
kind: route
title: "If an element of CT_P(Z) factors, on a clopen invariant subset of the profinite integers, onto an infinite minimal subshift whose topological full group contains an infinite finitely generated periodic group, that group lies in CT_P(Z); with a Grigorchuk subshift this answers Kourovka 19.46 and 17.58 positively"
target: ct-z-has-an-infinite-finitely-generated-periodic-subgroup
requires:
  - aperiodic-full-groups-lift-along-factor-maps
  - ct-p-z-is-a-one-vertex-k-graph-full-group
  - ct-p-z-recurrent-slope-tails-force-isometric-minimal-sets
---

**Route (conditional; the condition is OPEN).** Lane proof by bh-1946, elementary. It is the
CT(Z) analogue of `nv-periodic-groups-via-schreier-subshift-factors`.

**Hypothesis (F).** There are
- a finite set `P` of odd primes and `g ∈ CT_P(Z)`;
- a clopen `U ⊆ Ẑ = ∏_{p ∈ P ∪ {2}} Z_p` with `ĝ(U) = U`;
- an infinite minimal subshift `(X, T)` and a continuous surjection `π : U → X` with
  `π ∘ ĝ = T ∘ π`;

such that `[[T]]` contains an infinite finitely generated periodic group `Q`.

**Conclusion.** `Q` embeds in `CT_P(Z)`.

**Proof.**
- **Lifting.** `X` is infinite and minimal, so `T` is aperiodic. By
  `aperiodic-full-groups-lift-along-factor-maps` with `S = ĝ|_U`, `f ↦ f~` is an injective
  homomorphism `[[T]] → [[ĝ|_U]]`.
- **`[[ĝ|_U]]` lies in `CT_P(Z)`.** Take `f ∈ [[ĝ|_U]]`, extended by the identity off `U`.
  - Its cocycle is locally constant, so there is a partition of `Z` into finitely many residue
    classes with `P ∪ {2}`-smooth moduli, on each of which `f` equals a fixed power of `g`, or
    the identity.
  - Powers of `g` are canonical on a refinement, so `f` is given by canonical class maps.
  - `f` and `f^{-1}` map integers to integers, since powers of `g` do. So `f|_Z` is a
    permutation of `Z` of the form in item 3 of `ct-p-z-is-a-one-vertex-k-graph-full-group`,
    hence `f ∈ CT_P(Z)`.
- **Conclusion.** `Q ≅ Q~ ≤ CT_P(Z)`. ∎

**Candidates for `(X, T)`.**
- Matte Bon (arXiv:1408.0762; the abstract, as recorded in
  `nv-periodic-groups-via-schreier-subshift-factors`) embeds every Grigorchuk group `G_ω` in
  `[[T]]` for a minimal subshift.
- Grigorchuk's first group is an infinite finitely generated 2-group of intermediate growth.
  So (F) with its subshift answers both 19.46 and 17.58.
- Its subshift is a Toeplitz almost 1-1 extension of the 2-adic odometer, singular exactly
  over one orbit (recalled from Vorobets' description, not re-read).

**What any `(g, U)` satisfying (F) must look like**
(`ct-p-z-recurrent-slope-tails-force-isometric-minimal-sets`):
- **Not in V.** `g ∉ CT_∅(Z) ≅ V`: by item 6 of `conway-amusical-permutation-is-the-full-three-shift` (Brin's revealing pairs, recalled there), every minimal set of an element of V on `Ẑ` is an
  isometric extension of a finite orbit.
- **Aperiodic on `U`.** Equivalently, no finite cycle on `U ∩ Z_(P ∪ {2})`. This is
  achievable: the north-south element is aperiodic on `Z_2 × Z_3`.
- **Sweeping at all scales.** Along every orbit in `U`, in both time directions, the slope
  potential must dip below every level it reaches, by every amount. Otherwise `U` contains an
  odometer minimal set, which has no subshift factor.
- **A heuristic consequence (not proved).** No hyperbolic (full-shift-like) clopen invariant set works, since
  shadowing gives bounded-potential orbits.
- **The natural target.** An element whose slope cocycle along orbits is a Toeplitz-type sum,
  for example a renormalizable element that reproduces itself on a subclass after class
  conjugation.

## Attempts

- **1 (bh-1946, 09-19): an element of V.** The north-south `ψ ∈ V`, viewed in `CT_{3}(Z)`,
  is aperiodic on `Z_2 × Z_3`. But its minimal sets are the two odometer fibers over `−2/3` and
  `−1/3`, and its full group is torsion locally finite. It dies where
  `ct-p-z-recurrent-slope-tails-force-isometric-minimal-sets` predicts: forward potentials tend
  to `+∞` with no dips.
