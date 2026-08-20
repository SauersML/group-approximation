# The spectral route to `SharpExistence`

Status note, 2026-08-19.  Authored without a build (edit/write only), wired into
the root in the same pass.

## What `SharpExistence` is, and why it is still open here

`Kazhdan/TorsionFreeHyperbolicKazhdan.lean`:

```
SharpExistence : ∃ (G : Type) (_ : Group G),
  Infinite G ∧ Group.IsFinitelyPresented G ∧ IsPowerTorsionFree G ∧
    IsHyperbolicGroup G ∧ HasKazhdanPropertyT.{0,0} G
```

The literal three-clause statement without `Infinite` is degenerate (the trivial
group satisfies it), and `Multiplicative ℤ` satisfies every clause of
`SharpExistence` except property `(T)`.  So the whole content is `(T)` for an
infinite hyperbolic group, and there are exactly three known sources:

1. a torsion-free cocompact lattice in `Sp(n,1)`, `n ≥ 2` (Kostant for `(T)`,
   Selberg for torsion-freeness);
2. a random group at density `1/3 < d < 1/2` (Gromov; Ollivier; Żuk, as used by
   Ollivier--Wise);
3. a group acting properly cocompactly on a simply connected complex whose
   finite links have `λ₁ > 1/2` (Garland's method; Ballmann--Świątkowski; Żuk).

None is in Mathlib.  Sources 1 and 2 have inputs that are not finite objects.
Source 3 does: its input is a finite graph and an eigenvalue inequality.

**But there is a fourth source, and it is already formalized in this
repository.**  See the correction at the end of this note.

## What landed

`Kazhdan/OrbitAverageSpectralGap.lean` --- property `(T)` **is** a uniform norm
gap for the orbit average, proved in both directions:

* `OrbitAverageGap G S lam` --- in every complete orthogonal representation with
  no nonzero invariant vector, `‖|S|⁻¹ ∑_{q ∈ S} ρ(q) x‖ ≤ lam ‖x‖`;
* `isKazhdanPair_of_orbitAverageGap` --- a gap `lam < 1` is a Kazhdan pair at
  tolerance `1 - lam`.  No generation, symmetry or identity hypothesis on `S`;
* `orbitAverageGap_of_isKazhdanPair` --- the converse, from
  `IsKazhdanPair.norm_orbitAverage_le`, at `1 - ε²/(4|S|)`;
* `hasKazhdanPropertyT_iff_exists_orbitAverageGap` --- the equivalence;
* `weightedAverage` / `WeightedAverageGap` /
  `isKazhdanPair_of_weightedAverageGap` --- the same criterion for a convex
  combination `∑ w q • ρ(q) x`, at tolerance `(1 - lam)/2`.  This is the form
  Garland's method produces, because the operator it bounds is the Laplacian of
  a *weighted* graph; `weightedAverage_const` checks the uniform statement is
  the constant-weight case;
`Kazhdan/OrbitAverageFormGap.lean` --- the same criterion at the *quadratic
form*, which is where eigenvalues live:

* `WeightedFormGap G S w lam` --- `⟪∑ w q • ρ(q) x, x⟫ ≤ lam ‖x‖²`, a Rayleigh
  bound and nothing more;
* `isKazhdanPair_of_weightedFormGap` --- a Kazhdan pair at `(1 - lam)/2`, with
  **no** self-adjointness, positivity or symmetry hypothesis on the operator.
  This matters: turning a Rayleigh bound into a norm bound normally costs
  self-adjointness, and an orbit average is self-adjoint only when the alphabet
  is symmetric;
* `weightedFormGap_of_weightedAverageGap` --- the form gap is the weaker
  hypothesis, so this module subsumes the norm criterion.

`Kazhdan/OrbitAverageFiniteControl.lean` --- positive control, and sharp: a
finite group has gap constant `0` (`orbitAverageGap_univ_of_fintype`), whence
`hasKazhdanPropertyT_of_fintype`.  Kept in a separate module so the criterion
does not import a witness.

`Kazhdan/SharpExistenceSpectralRoute.lean` --- the third route:

* `SpectralRouteInput` --- `SharpExistence` with the `(T)` clause replaced by
  the certificate `(gapSet, gapConstant, gap)`;
* `sharpExistence_of_spectralRoute` --- reaches `SharpExistence` **taking no
  hypothesis beyond the input**.  Contrast `sharpExistence_of_latticeRoute`,
  which takes three permanence properties, one of them an instance of the Morse
  lemma;
* `spectralRouteInput_of_sharpExistence` and
  `sharpExistence_iff_nonempty_spectralRouteInput` --- the honest half: the
  criterion is an equivalence, so this route relocates the difficulty and does
  not reduce it;
* `not_exists_orbitAverageGap_multiplicative_int` --- negative control: the
  infinite cyclic group carries no certificate.

## What the measurement says

**Correction, same day.**  An earlier version of this note said the property
`(T)` clause of `SharpExistence` is the part with no formalized source.  That is
**false about this repository**, and the error was mine for not reading
`GroupApproximation/PropertyT/` and `Kazhdan/ExactHodgeCertificate.lean` before
writing it.

Two things are already here:

* **Property `(T)` for infinite groups, unconditionally.**
  `PropertyT/FreeElementaryPropertyT.freeElementary_hasKazhdanPropertyT` proves
  it for `EL₃(𝔽₂⟨X⟩)` (Ershov--Jaikin-Zapirain in characteristic two, via the
  `A₂` codistance estimate), and
  `PropertyT/FiniteTypeCharacteristicTwoPropertyT` descends it to every
  finite-type `𝔽₂`-algebra.  `Leavitt/ElementaryGroup.elementaryGroup_infinite`
  gives infiniteness.  So (T) for an infinite group is **done**.
* **A general, group-agnostic certificate machine.**
  `Kazhdan/ExactHodgeCertificate.Certificate.hasKazhdanPropertyT` takes *any*
  group `G`, any finite generating tuple `s : I → G`, and a finite **rational**
  Hodge/sum-of-squares certificate over `ℚ[G]` --- a Gram decomposition of the
  Hodge matrix with `ℓ¹`-controlled residual --- and returns
  `HasKazhdanPropertyT`.  This is the Ozawa / Netzer--Thom positivity route, the
  one Kaluba--Nowak--Ozawa used for `SL₃(ℤ)` and `Aut(F₅)`.  No Garland, no Żuk,
  no Kostant is needed to use it.

So the honest location of the gap is **not** the analytic content of `(T)`.
`Kazhdan/CharTwoTorsionObstruction.lean` proves where it actually is:

* `elementaryThree_not_isPowerTorsionFree` --- in characteristic two every root
  element is an involution (`x_{ij}(a)² = x_{ij}(a+a) = 1`), so the formalized
  Kazhdan family is **not torsion-free**;
* `subsingleton_of_isPowerTorsionFree_quotient_elementaryThree` --- and no
  quotient repairs it, even though `(T)` passes to quotients: a group generated
  by involutions has no nontrivial torsion-free quotient;
* `elementaryThree_kazhdan_and_not_torsionFree` --- the two halves side by side.

The same structural fact blocks hyperbolicity: `X₁₂` and `X₁₃` commute, so
`EL₃(R)` contains an infinite subgroup of exponent two, and hyperbolic groups
have bounded torsion.

## The certificate route, wired

`Kazhdan/SharpExistenceCertificateRoute.lean` connects the two:

* `sharpExistence_of_hodgeCertificate` --- given a finitely presented, infinite,
  torsion-free group that is hyperbolic in the four-point sense, together with a
  finite rational Hodge certificate for one finite generating tuple,
  `SharpExistence` follows.  No mathematical hypothesis beyond the data.

This is the **first route recorded here whose input is not known to be
equivalent to its conclusion**.  The random-group route
(`randomGroupInput_of_sharpExistence`) and the spectral route
(`spectralRouteInput_of_sharpExistence`) both come with proved converses, so
both are citations.  The converse here would be Ozawa's theorem that a `(T)`
group admits such a certificate, which is not formalized, so this is a genuine
reduction --- to finite rational data.

## The hyperbolicity half, built

`Algebra/ListCommonPrefix.lean` + `Algebra/TreeLikeHyperbolic.lean` +
`Algebra/HyperbolicFreeGroup.lean`:

* `Hyperbolic.IsTreeLike S p` --- a common-prefix length with the cancellation
  identity `d(x,y) + 2 p x y = |x| + |y|` and the ultrametric inequality
  `min (p x z) (p y z) ≤ p x y`;
* `isHyperbolicGroup_of_isTreeLike` --- those two lines give `δ = 0`
  hyperbolicity, because `isFourPointHyperbolic_iff_gromovProduct` already says
  the four-point condition *is* Gromov's product condition, and under
  `IsTreeLike` the Gromov product is literally `2 p (w⁻¹x) (w⁻¹y)`;
* `isHyperbolicGroup_freeGroup` --- **a free group of finite rank is
  `0`-hyperbolic**, the first nonelementary hyperbolic group in the library.
  The content is `norm_inv_mul_add_two_mul_lcp`: `x⁻¹y` is
  `mk (invRev (drop k u) ++ drop k v)` with `k` the common prefix length, and
  that word is reduced because past the prefix the two reduced words disagree.

`Kazhdan/FreeGroupSharpProfile.lean` assembles the consequence:
`freeGroup_sharpProfile_and_not_kazhdan` proves a free group of finite rank
satisfies **four of the five clauses** of `SharpExistence` --- infinite,
finitely presented, torsion-free, hyperbolic --- and fails the fifth, property
`(T)`, necessarily: it surjects onto `Multiplicative ℤ`, `(T)` passes to
quotients, and the infinite cyclic group is not Kazhdan.

That locates the remaining work exactly: it is a certificate for a *different*
group, not more hyperbolicity theory.

## What actually remains

Reaching `SharpExistence` now needs **two finite objects**, not a deep theorem:

1. **An explicit finite presentation** of a group that is infinite, torsion-free
   and hyperbolic in the four-point sense of `Algebra/HyperbolicGroup.lean`.
   Proving hyperbolicity for a concrete presentation is the hard half, but it
   is no longer unstarted: `IsTreeLike` handles the tree case and a free group
   is now proved `0`-hyperbolic, which is the base case every
   small-cancellation or Bass--Serre argument builds on.
2. **A rational Hodge certificate** for that presentation, which
   `ExactHodgeCertificate.Certificate.hasKazhdanPropertyT` then turns into
   property `(T)`.  Producing one is a numerical SDP solve plus rational
   rounding --- computational work, not a formalization of a deep theorem.

The catch is that no published SOS certificate is known to the author of this
note for a *hyperbolic* `(T)` group: the certificates in the literature are for
`SL₃(ℤ)`, `SL₄(ℤ)`, `Aut(F₅)` and relatives, none of which is hyperbolic
(all contain `ℤ²`).  The known hyperbolic `(T)` groups are the `Sp(n,1)`
lattices and the Ballmann--Świątkowski/Żuk complexes, and for those the
certificate has to be produced, not cited.

So `SharpExistence` is *not* proved, is not assumed anywhere, and the two
remaining pieces are of different kinds: item 2 is a computation (an SDP solve
plus rational rounding, run against a concrete hyperbolic presentation), item 1's
hyperbolicity clause is mathematics that nobody here has done --- the library
proves hyperbolicity only for finite groups, the trivial group and
`Multiplicative ℤ`, and the first nonelementary example (a free group, whose
Cayley graph is a tree) is still missing.

Everything else --- the whole analytic content of property `(T)` --- is
already discharged in this repository.
