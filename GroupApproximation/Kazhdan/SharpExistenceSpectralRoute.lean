import GroupApproximation.Kazhdan.TorsionFreeHyperbolicKazhdan
import GroupApproximation.Kazhdan.OrbitAverageSpectralGap

/-!
# The spectral route to `SharpExistence`

`Kazhdan/SharpExistenceRoutes.lean` records the two routes the literature takes
to `SharpExistence` --- an infinite, finitely presented, torsion-free hyperbolic
group with property `(T)` --- and measures what each costs.  The random-group
route turned out to be a citation: its input structure is *equivalent* to the
conclusion.  The lattice route is a genuine reduction, but to three permanence
properties, one of which is an instance of the Morse lemma.

This module adds the third route, the one the proofs of property `(T)` for
infinite groups actually run along, and measures it the same way.

## What changes

`SpectralRouteInput` is `SharpExistence` with the property `(T)` clause replaced
by a **finite spectral certificate**: a nonempty finite subset `S` of the group
and a constant `lam < 1` such that the orbit average over `S` has norm at most
`lam` in every orthogonal representation with no invariant vector
(`SpectralGap.OrbitAverageGap`).  `sharpExistence_of_spectralRoute` reaches
`SharpExistence` from that input **with no further hypothesis** --- no
permanence property, no quasi-isometry invariance, no Morse lemma --- which is
what distinguishes this route from the lattice one.

The reason it can be unconditional is `Kazhdan/OrbitAverageSpectralGap.lean`:
the passage from a gap to a Kazhdan pair is proved there, at the explicit
tolerance `1 - lam`, rather than quoted.

## What does not change

The route is still not a decomposition of the problem, and this module says so
in the same way the random-group route is measured:
`spectralRouteInput_of_sharpExistence` proves the converse, so
`sharpExistence_iff_nonempty_spectralRouteInput` is an equivalence.  That is
forced --- `SpectralGap.hasKazhdanPropertyT_iff_exists_orbitAverageGap` is an
equivalence, and the other four clauses are copied across unchanged --- and it
is the honest reading: **replacing `(T)` by a spectral gap moves the difficulty,
it does not reduce it.**

What the move buys is that the remaining difficulty is now of a *checkable
kind*.  A gap is an inequality between two explicitly given real numbers in each
representation; the theorems that supply one --- Garland's method as used by
Ballmann and Świątkowski, and Żuk's criterion, which bound the Laplacian of a
group acting on a simply connected complex by the smallest positive eigenvalue
of its finite links --- end exactly at
`SpectralGap.OrbitAverageGap`, and their input is a finite graph.  The lattice
route's input, by contrast, is a cocompact lattice in `Sp(n,1)` together with
Kostant's theorem and Selberg's lemma, none of which is a finite object.

So the measurement recorded here is: of the three routes to `SharpExistence`,
this is the only one whose property `(T)` clause is separated from the
conclusion by a statement about a finite object.

## The controls

`not_exists_orbitAverageGap_multiplicative_int` is the negative control: the
infinite cyclic group --- which satisfies every other clause of
`SharpExistence`, by `Hyperbolic.exists_infinite_torsionFree_hyperbolic_not_kazhdan`
--- has **no** spectral certificate, so the certificate is not something every
infinite hyperbolic group carries.  `SpectralGap.orbitAverageGap_univ_of_fintype`
is the positive control on the other side, and it is sharp: a finite group has
gap constant `0`.  Together they say the gap sees exactly the distinction the
statement is about, and `trivialWitness` cannot sneak in, because
`SpectralRouteInput` carries `Infinite` as a field.

Nothing here proves `SharpExistence`, nothing here assumes it, and no
declaration below is conditional on it.
-/

namespace GroupApproximation
namespace Hyperbolic

/-! ## The route -/

/-- **The spectral route's input.**  `SharpExistence` with property `(T)`
replaced by a finite spectral certificate for the orbit average.

Every field but the last three is a clause of `SharpExistence` carried across
unchanged; `gapSet`, `gapConstant` and `gap` are the certificate that stands in
for property `(T)`.  `Infinite` is a field, so the degenerate witness of
`Kazhdan/TorsionFreeHyperbolicKazhdan.lean` does not inhabit this structure. -/
structure SpectralRouteInput where
  /-- The group. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [fpCarrier : Group.IsFinitelyPresented Carrier]
  [infiniteCarrier : Infinite Carrier]
  /-- Torsion-free. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- Hyperbolic, in the four-point sense of `Algebra/HyperbolicGroup.lean`. -/
  hyperbolic : IsHyperbolicGroup Carrier
  /-- The alphabet the certificate averages over. -/
  gapSet : Finset Carrier
  /-- It is nonempty, so that the average is an average. -/
  gapSetNonempty : gapSet.Nonempty
  /-- The contraction factor. -/
  gapConstant : ℝ
  /-- It is a strict contraction. -/
  gapLt : gapConstant < 1
  /-- **The certificate.**  In every complete orthogonal representation with no
  nonzero invariant vector, the orbit average over `gapSet` contracts by
  `gapConstant`.  This is what a formalization of Żuk's criterion would
  produce. -/
  gap : SpectralGap.OrbitAverageGap.{0, 0} Carrier gapSet gapConstant

instance spectralRouteInputGroup (P : SpectralRouteInput) : Group P.Carrier :=
  P.groupCarrier

/-- **The spectral route reaches the sharp statement, and takes nothing else.**

Compare `sharpExistence_of_latticeRoute`, which needs three permanence
properties: here the property `(T)` clause is discharged by
`SpectralGap.hasKazhdanPropertyT_of_orbitAverageGap`, which is proved and not
assumed, so this theorem has exactly one hypothesis --- the input itself. -/
theorem sharpExistence_of_spectralRoute (P : SpectralRouteInput) :
    SharpExistence :=
  ⟨P.Carrier, P.groupCarrier, P.infiniteCarrier, P.fpCarrier, P.torsionFree,
    P.hyperbolic,
    SpectralGap.hasKazhdanPropertyT_of_orbitAverageGap
      P.gapSetNonempty P.gapLt P.gap⟩

/-- ... and the sharp statement reaches the input.  This is the honest
measurement, and it is the same verdict `randomGroupInput_of_sharpExistence`
returns for the random-group route: the spectral certificate is equivalent to
the conclusion, so this route relocates the difficulty rather than reducing it.
What it relocates it *to* is a statement about a finite object, which is the
point of the exercise. -/
theorem spectralRouteInput_of_sharpExistence (h : SharpExistence) :
    Nonempty SpectralRouteInput := by
  obtain ⟨G, inst, hinf, hfp, htf, hhyp, hT⟩ := h
  letI : Group G := inst
  obtain ⟨S, lam, hS, hlam, hgap⟩ :=
    SpectralGap.exists_orbitAverageGap_of_hasKazhdanPropertyT hT
  exact ⟨{ Carrier := G
           groupCarrier := inst
           fpCarrier := hfp
           infiniteCarrier := hinf
           torsionFree := htf
           hyperbolic := hhyp
           gapSet := S
           gapSetNonempty := hS
           gapConstant := lam
           gapLt := hlam
           gap := hgap }⟩

/-- **The spectral route is exactly the sharp statement.**  Stated so that the
equivalence is machine-checked rather than left as a remark in the docstring. -/
theorem sharpExistence_iff_nonempty_spectralRouteInput :
    SharpExistence ↔ Nonempty SpectralRouteInput :=
  ⟨spectralRouteInput_of_sharpExistence,
    fun h ↦ h.elim sharpExistence_of_spectralRoute⟩

/-! ## The negative control

The certificate is not free: an infinite group can satisfy every other clause of
`SharpExistence` and carry no gap at all. -/

/-- **The infinite cyclic group has no spectral certificate.**  It is infinite,
torsion-free and `0`-hyperbolic --- `exists_infinite_torsionFree_hyperbolic_not_kazhdan`
--- so this is the exact statement that the gap, and not any of the other four
clauses, is the content of `SharpExistence`. -/
theorem not_exists_orbitAverageGap_multiplicative_int :
    ¬ ∃ S : Finset (Multiplicative ℤ), ∃ lam : ℝ,
        S.Nonempty ∧ lam < 1 ∧
          SpectralGap.OrbitAverageGap.{0, 0} (Multiplicative ℤ) S lam := by
  intro h
  refine not_hasKazhdanPropertyT_multiplicative_int ?_
  exact SpectralGap.hasKazhdanPropertyT_iff_exists_orbitAverageGap.mpr h

end Hyperbolic
end GroupApproximation
