import GroupApproximation.GGT.KazhdanHypGirthEight

/-!
# Infiniteness is not an input in the positive triangular Kazhdan route

Every positive triangular presentation has a canonical quotient onto the
cyclic group of order three: send every generator to `1 mod 3`.  Each defining
relator has three positive letters, hence dies in that quotient.  In
particular, the presented group is nontrivial.  If it is torsion-free, it is
therefore infinite, since a finite torsion-free group is trivial.

This removes the `Infinite` field from the concrete girth-eight route to
`Hyperbolic.SharpExistence`.  The remaining non-finite obligations are exactly
the two geometric conclusions that `C(3)`--`T(8)` is meant to provide:
torsion-freeness and hyperbolicity.  Property `(T)`, finite presentation,
nontriviality, and infiniteness are all derived.
-/

namespace GroupApproximation
namespace KazhdanHyp

open FoxBoundary PresentedGroupRelatorReplay

section CyclicThreeQuotient

variable {Generator TriangleIndex : Type} [Fintype Generator]
  [DecidableEq Generator] [Nonempty Generator] [Fintype TriangleIndex]
  [DecidableEq TriangleIndex]

/-- The distinguished generator of the cyclic group of order three. -/
def cyclicThreeGenerator : Multiplicative (ZMod 3) :=
  Multiplicative.ofAdd (1 : ZMod 3)

theorem cyclicThreeGenerator_ne_one : cyclicThreeGenerator ≠ 1 := by
  intro h
  have h' : (1 : ZMod 3) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa [cyclicThreeGenerator] using this
  exact absurd h' (by decide)

theorem cyclicThreeGenerator_cube : cyclicThreeGenerator ^ 3 = 1 := by
  show Multiplicative.ofAdd (1 : ZMod 3) ^ 3 = 1
  rw [← ofAdd_nsmul, ← ofAdd_zero]
  congr 1
  decide

omit [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- A positive triangular relator evaluates to one when every generator is
sent to the distinguished element of `C₃`. -/
theorem cyclicThree_lift_relator_eq_one
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ j k, (T j k).2 = true) (j : TriangleIndex) :
    FreeGroup.lift (fun _ : Generator ↦ cyclicThreeGenerator)
        (TriangularHodgeLayer.relator (T j)) = 1 := by
  unfold TriangularHodgeLayer.relator
  rw [← wordValue_freeGroup_map]
  rw [TriangularHodgeLayer.letters_eq_three]
  simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    FreeGroup.lift_apply_of, letterValue, hpositive j 0, hpositive j 1,
    hpositive j 2, if_true, mul_one]
  simpa [pow_three] using cyclicThreeGenerator_cube

omit [Nonempty Generator] [DecidableEq TriangleIndex] in
/-- The constant assignment to `C₃` kills the full relator set. -/
theorem cyclicThree_kills_relators
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ j k, (T j k).2 = true) :
    ∀ r ∈ (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)),
      FreeGroup.lift (fun _ : Generator ↦ cyclicThreeGenerator) r = 1 := by
  intro r hr
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hr)
  exact cyclicThree_lift_relator_eq_one T hpositive j

/-- The canonical quotient of a positive triangular presentation onto `C₃`. -/
def cyclicThreeQuotient
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ j k, (T j k).2 = true) :
    TriangularHodgeLayer.Presented T →* Multiplicative (ZMod 3) :=
  PresentedGroup.toGroup (cyclicThree_kills_relators T hpositive)

omit [Nonempty Generator] [DecidableEq TriangleIndex] in
@[simp] theorem cyclicThreeQuotient_generator
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ j k, (T j k).2 = true) (i : Generator) :
    cyclicThreeQuotient T hpositive (TriangularHodgeLayer.generator T i) =
      cyclicThreeGenerator :=
  PresentedGroup.toGroup.of _

omit [Nonempty Generator] [DecidableEq TriangleIndex] in
/-- Every canonical generator of a positive triangular presentation is
nontrivial.  The proof is witnessed by its image in `C₃`. -/
theorem generator_ne_one_of_positive
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ j k, (T j k).2 = true) (i : Generator) :
    TriangularHodgeLayer.generator T i ≠ 1 := by
  intro hi
  have himage := congrArg (cyclicThreeQuotient T hpositive) hi
  rw [cyclicThreeQuotient_generator, map_one] at himage
  exact cyclicThreeGenerator_ne_one himage

omit [DecidableEq TriangleIndex] in
/-- A positive triangular presentation which is torsion-free is infinite.

This is the exact replacement for the independent `Infinite` premise in the
old endpoint: positivity gives a nontrivial `C₃` quotient, while a finite
torsion-free group is subsingleton. -/
theorem infinite_of_positive_of_torsionFree
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ j k, (T j k).2 = true)
    (htf : IsPowerTorsionFree (TriangularHodgeLayer.Presented T)) :
    Infinite (TriangularHodgeLayer.Presented T) := by
  apply Infinite.of_not_fintype
  intro hfinite
  letI : Fintype (TriangularHodgeLayer.Presented T) := hfinite
  let i : Generator := Classical.choice inferInstance
  have hsub : Subsingleton (TriangularHodgeLayer.Presented T) :=
    Hyperbolic.subsingleton_of_finite_of_isPowerTorsionFree htf
  exact generator_ne_one_of_positive T hpositive i (hsub.elim _ _)

end CyclicThreeQuotient

/-! ## The reduced sharp endpoint -/

/-- Torsion-freeness alone supplies the old independent infiniteness residual
for girth-eight tables. -/
theorem girthEightInfinite_of_torsionFree (htf : GirthEightTorsionFree) :
    GirthEightInfinite := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  exact infinite_of_positive_of_torsionFree T hchecks.1
    (htf Generator TriangleIndex fg dg ng ft dt T d hchecks)

/-- **The strongest concrete girth-eight construction target.**

The same finite table carries the sparse girth-eight check and the exact
rational Garland/SDP certificate.  Only torsion-freeness and hyperbolicity of
its presented group remain.  Infiniteness is deliberately absent: it follows
from positivity, the canonical `C₃` quotient, and torsion-freeness. -/
def GirthEightKazhdanConstruction : Prop :=
  ∃ (Generator TriangleIndex Row : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex) (_ : Fintype Row)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ) (gap : ℚ)
    (rows : Row → Generator × Bool → ℚ),
    GirthEightChecks T d ∧ GirthEightSDPChecks T d gap rows ∧
      IsPowerTorsionFree (TriangularHodgeLayer.Presented T) ∧
      Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T)

/-- A girth-eight construction closes `SharpExistence`.  The finite checks
give property `(T)`; the presentation gives finite presentation; positivity
and torsion-freeness give infiniteness. -/
theorem sharpExistence_of_girthEightKazhdanConstruction
    (h : GirthEightKazhdanConstruction) : Hyperbolic.SharpExistence := by
  obtain ⟨Generator, TriangleIndex, Row, fg, dg, ng, ft, dt, fr, T, d, gap, rows,
    hgeom, hsdp, htf, hhyp⟩ := h
  exact ⟨TriangularHodgeLayer.Presented T, inferInstance,
    infinite_of_positive_of_torsionFree T hgeom.1 htf, inferInstance, htf, hhyp,
    hasKazhdanPropertyT_of_girthEightSDPChecks hgeom hsdp⟩

/-- Universal `C(3)`--`T(8)` torsion-freeness and hyperbolicity plus one table
passing both finite checks suffice; no infiniteness theorem is needed. -/
theorem sharpExistence_of_girthEightChecks
    (htf : GirthEightTorsionFree) (hhyp : GirthEightHyperbolicity)
    {Generator TriangleIndex Row : Type} [fg : Fintype Generator]
    [dg : DecidableEq Generator] [ng : Nonempty Generator]
    [ft : Fintype TriangleIndex] [dt : DecidableEq TriangleIndex] [fr : Fintype Row]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ) (gap : ℚ)
    (rows : Row → Generator × Bool → ℚ)
    (hgeom : GirthEightChecks T d) (hsdp : GirthEightSDPChecks T d gap rows) :
    Hyperbolic.SharpExistence :=
  sharpExistence_of_girthEightKazhdanConstruction ⟨Generator, TriangleIndex, Row,
    fg, dg, ng, ft, dt, fr, T, d, gap, rows, hgeom, hsdp,
    htf Generator TriangleIndex fg dg ng ft dt T d hgeom,
    hhyp Generator TriangleIndex fg dg ng ft dt T d hgeom⟩

end KazhdanHyp
end GroupApproximation
