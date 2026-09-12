import GroupApproximation.PropertyT.IntegralGeneratorShearDescent

/-!
# Selecting one descent letter, measurably

`IntegralGeneratorShearDescent` proves that a character of the integral column
plane whose valuation in one root coordinate is positive admits an alphabet
letter along which that valuation descends by exactly one, and that the shear
by such a letter moves the character's `A/B/C/D` region one degree stage down.
A mass comparison needs more than the pointwise statement: the source region
must be cut into finitely many *measurable* pieces, one per letter, whose
images under the corresponding shears are pairwise disjoint.  Otherwise the
`|X|` shears each pay for the whole target and the estimate loses a factor
`|X|` per stage, which no fixed point can absorb.

This file supplies that cut.  For each letter `x` the set of characters along
which `x` realizes the descent is Borel, because it is the finite union, over
the words of length at most the stage, of a least-degree fibre intersected
with the nontrivial set of a single coefficient coordinate.  Nested
differences then turn the `|X|` overlapping sets into a disjoint cover.

Disjointness of the *images* is the point of `descentSet_lowerCharacterAction`:
a lower shear does not touch the second root coordinate at all, so it
preserves the whole set of descent letters of that coordinate, and the image
of the `i`-th piece lands in the `i`-th piece of the target decomposition.
This is the integral form of the selector bookkeeping in
`FreeRootPlaneMass.sum_planeMass_AB_le_coarse_CD`, where the target sum is
filtered by `leastLeadingGeneratorIndex` for exactly this reason.
-/

namespace GroupApproximation
namespace IntegralGeneratorShearSelector

open Set MeasureTheory WeakDual
open IntegralCharacterMass
open IntegralColumnPlaneSpectralMeasure
open IntegralColumnPlaneSpectralShear
open IntegralColumnPlaneSpectralTorus
open IntegralColumnPlaneSpectralMassBound
open IntegralGeneratorShearDescent
open FreeAlgebraDegree

noncomputable section

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {X : Type u} [Fintype X]
variable (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))

noncomputable local instance columnPlaneCharacterMeasurableSpace :
    MeasurableSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  borel _

local instance columnPlaneCharacterBorelSpace :
    BorelSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  ⟨rfl⟩

/-! ### One coefficient coordinate as a Borel set -/

omit [Fintype X] in
/-- The characters nontrivial at one coefficient coordinate form the
one-element case of the finite detection sets, hence a Borel set. -/
theorem coordinateAngle_ne_zero_setOf_eq
    (q : Fin 2 × FreeAlgebra ℤ X) :
    {chi : characterSpace ℂ (representedColumnPlane rho).algebra |
        coordinateAngle rho q chi ≠ 0} =
      finitePlaneNontrivialSet rho {q} := by
  ext chi
  constructor
  · intro hchi
    refine ⟨q, Finset.mem_singleton_self q, ?_⟩
    exact fun hone ↦ hchi ((coordinateAngle_eq_zero_iff rho q chi).mpr hone)
  · rintro ⟨p, hp, hne⟩
    rw [Finset.mem_singleton] at hp
    subst hp
    exact fun hzero ↦ hne ((coordinateAngle_eq_zero_iff rho _ chi).mp hzero)

omit [Fintype X] in
theorem measurableSet_coordinateAngle_ne_zero
    (q : Fin 2 × FreeAlgebra ℤ X) :
    MeasurableSet
      {chi : characterSpace ℂ (representedColumnPlane rho).algebra |
        coordinateAngle rho q chi ≠ 0} := by
  rw [coordinateAngle_ne_zero_setOf_eq]
  exact measurableSet_finitePlaneNontrivialSet rho _

/-! ### The descent set of one letter -/

/-- The characters whose least visible degree in root coordinate `b` at stage
`n` is realized, one letter down, along `x`. -/
def descentSet (b : Fin 2) (n : ℕ) (x : X) :
    Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  {chi | ∃ w : FreeMonoid X,
    freeWordLength X w + 1 = leastRootWordDegreeWithin rho b n chi ∧
    coordinateAngle rho (b, FreeAlgebra.ι ℤ x * wordMonomial X ℤ w) chi ≠ 0}

/-- The descent set is a finite union of least-degree fibres cut by single
coefficient coordinates.  Only words of length at most the stage occur,
because the least degree never exceeds `n + 1`. -/
theorem descentSet_eq_biUnion (b : Fin 2) (n : ℕ) (x : X) :
    descentSet rho b n x =
      ⋃ w ∈ (freeWordsLE X n : Finset (FreeMonoid X)),
        (rootWordDegreeFiber rho b n (freeWordLength X w + 1) ∩
          {chi | coordinateAngle rho
            (b, FreeAlgebra.ι ℤ x * wordMonomial X ℤ w) chi ≠ 0}) := by
  ext chi
  constructor
  · rintro ⟨w, hlen, hne⟩
    have hle : freeWordLength X w ≤ n := by
      have hsucc := leastRootWordDegreeWithin_le_succ rho b n chi
      omega
    exact Set.mem_biUnion
      (Finset.mem_coe.mpr ((mem_freeWordsLE X w n).mpr hle))
      ⟨hlen.symm, hne⟩
  · intro hchi
    obtain ⟨w, -, hfiber, hne⟩ := Set.mem_iUnion₂.mp hchi
    exact ⟨w, hfiber.symm, hne⟩

theorem measurableSet_descentSet (b : Fin 2) (n : ℕ) (x : X) :
    MeasurableSet (descentSet rho b n x) := by
  rw [descentSet_eq_biUnion]
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun w _ ↦ ?_
  exact (measurableSet_rootWordDegreeFiber rho b n _).inter
    (measurableSet_coordinateAngle_ne_zero rho _)

/-- Every character with a positive least visible degree lies in the descent
set of some letter.  This is `exists_generator_descent`, restated for the
partition. -/
theorem exists_mem_descentSet (b : Fin 2) (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho b n)
    (hpos : 0 < leastRootWordDegreeWithin rho b n chi) :
    ∃ x : X, chi ∈ descentSet rho b n x := by
  obtain ⟨x, w, hlen, hne⟩ := exists_generator_descent rho b n chi hvis hpos
  exact ⟨x, w, hlen, hne⟩

/-! ### The descent set is carried along by the shear that does not touch it -/

/-- A lower shear leaves every second-coordinate descent set invariant, in
both directions and at any stage.  This is what makes the images of the
different letter pieces disjoint. -/
theorem descentSet_lowerCharacterAction (r : FreeAlgebra ℤ X) (n : ℕ) (x : X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    lowerCharacterAction rho r chi ∈ descentSet rho 1 n x ↔
      chi ∈ descentSet rho 1 n x := by
  constructor
  · rintro ⟨w, hlen, hne⟩
    refine ⟨w, ?_, ?_⟩
    · rwa [leastRootWordDegreeWithin_lowerCharacterAction_one] at hlen
    · rwa [coordinateAngle_lowerCharacterAction_one] at hne
  · rintro ⟨w, hlen, hne⟩
    refine ⟨w, ?_, ?_⟩
    · rwa [leastRootWordDegreeWithin_lowerCharacterAction_one]
    · rwa [coordinateAngle_lowerCharacterAction_one]

/-- The mirror statement: an upper shear leaves every first-coordinate descent
set invariant. -/
theorem descentSet_upperCharacterAction (r : FreeAlgebra ℤ X) (n : ℕ) (x : X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    upperCharacterAction rho r chi ∈ descentSet rho 0 n x ↔
      chi ∈ descentSet rho 0 n x := by
  constructor
  · rintro ⟨w, hlen, hne⟩
    refine ⟨w, ?_, ?_⟩
    · rwa [leastRootWordDegreeWithin_upperCharacterAction_zero] at hlen
    · rwa [coordinateAngle_upperCharacterAction_zero] at hne
  · rintro ⟨w, hlen, hne⟩
    refine ⟨w, ?_, ?_⟩
    · rwa [leastRootWordDegreeWithin_upperCharacterAction_zero]
    · rwa [coordinateAngle_upperCharacterAction_zero]

/-- The descent set depends on the stage only through the least degree, so it
is unchanged whenever that value is. -/
theorem descentSet_stage_congr (b : Fin 2) (n m : ℕ) (x : X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hstage : leastRootWordDegreeWithin rho b m chi =
      leastRootWordDegreeWithin rho b n chi) :
    chi ∈ descentSet rho b m x ↔ chi ∈ descentSet rho b n x := by
  constructor
  · rintro ⟨w, hlen, hne⟩
    exact ⟨w, by omega, hne⟩
  · rintro ⟨w, hlen, hne⟩
    exact ⟨w, by omega, hne⟩

/-! ### The disjoint letter cut -/

/-- A chosen enumeration of the alphabet.  Only its injectivity is used. -/
def letterIndex : X ≃ Fin (Fintype.card X) := Fintype.equivFin X

/-- The `i`-th piece of the descent cut: the characters whose descent is
realized by the `i`-th letter and by no earlier one. -/
def descentPiece (b : Fin 2) (n : ℕ) (i : Fin (Fintype.card X)) :
    Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  descentSet rho b n ((letterIndex (X := X)).symm i) \
    ⋃ j ∈ {j : Fin (Fintype.card X) | j < i},
      descentSet rho b n ((letterIndex (X := X)).symm j)

theorem measurableSet_descentPiece (b : Fin 2) (n : ℕ)
    (i : Fin (Fintype.card X)) :
    MeasurableSet (descentPiece rho b n i) := by
  refine (measurableSet_descentSet rho b n _).diff ?_
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro j _
  exact measurableSet_descentSet rho b n _

theorem descentPiece_subset (b : Fin 2) (n : ℕ)
    (i : Fin (Fintype.card X)) :
    descentPiece rho b n i ⊆
      descentSet rho b n ((letterIndex (X := X)).symm i) :=
  fun _ hchi ↦ hchi.1

/-- Distinct pieces of the cut are disjoint. -/
theorem disjoint_descentPiece (b : Fin 2) (n : ℕ)
    {i j : Fin (Fintype.card X)} (hij : i ≠ j) :
    Disjoint (descentPiece rho b n i) (descentPiece rho b n j) := by
  rw [Set.disjoint_left]
  intro chi hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hj.2 (Set.mem_biUnion (by exact hlt) hi.1)
  · exact hi.2 (Set.mem_biUnion (by exact hgt) hj.1)

/-- The cut covers every character that has some descent letter. -/
theorem exists_mem_descentPiece (b : Fin 2) (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho b n)
    (hpos : 0 < leastRootWordDegreeWithin rho b n chi) :
    ∃ i : Fin (Fintype.card X), chi ∈ descentPiece rho b n i := by
  classical
  obtain ⟨x, hx⟩ := exists_mem_descentSet rho b n chi hvis hpos
  have hnonempty : ((Finset.univ : Finset (Fin (Fintype.card X))).filter
      (fun i ↦ chi ∈ descentSet rho b n
        ((letterIndex (X := X)).symm i))).Nonempty := by
    refine ⟨letterIndex (X := X) x, ?_⟩
    simpa using hx
  set i := ((Finset.univ : Finset (Fin (Fintype.card X))).filter
    (fun i ↦ chi ∈ descentSet rho b n
      ((letterIndex (X := X)).symm i))).min' hnonempty with hidef
  refine ⟨i, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hnonempty)).2
  · intro hmem
    obtain ⟨j, hj, hjmem⟩ := Set.mem_iUnion₂.mp hmem
    have hjfilter : j ∈ (Finset.univ : Finset (Fin (Fintype.card X))).filter
        (fun i ↦ chi ∈ descentSet rho b n
          ((letterIndex (X := X)).symm i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjmem⟩
    exact absurd (Finset.min'_le _ j hjfilter) (not_le.mpr hj)

/-! ### Bundled measurable equivalences of the two shears -/

/-- The dual action of a lower shear, as a measurable equivalence of the
character space. -/
def lowerCharacterMeasurableEquiv (r : FreeAlgebra ℤ X) :
    characterSpace ℂ (representedColumnPlane rho).algebra ≃ᵐ
      characterSpace ℂ (representedColumnPlane rho).algebra :=
  (CommutativeCStarCovariance.characterHomeomorph
    (representedColumnPlane rho).algebra
    ((representedColumnPlane rho).rho (lowerShear r))
    (lowerShear_forward rho r) (lowerShear_backward rho r)).toMeasurableEquiv

omit [Fintype X] in
@[simp] theorem lowerCharacterMeasurableEquiv_apply (r : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    lowerCharacterMeasurableEquiv rho r chi = lowerCharacterAction rho r chi :=
  rfl

/-- The dual action of an upper shear, as a measurable equivalence. -/
def upperCharacterMeasurableEquiv (r : FreeAlgebra ℤ X) :
    characterSpace ℂ (representedColumnPlane rho).algebra ≃ᵐ
      characterSpace ℂ (representedColumnPlane rho).algebra :=
  (CommutativeCStarCovariance.characterHomeomorph
    (representedColumnPlane rho).algebra
    ((representedColumnPlane rho).rho (upperShear r))
    (upperShear_forward rho r) (upperShear_backward rho r)).toMeasurableEquiv

omit [Fintype X] in
@[simp] theorem upperCharacterMeasurableEquiv_apply (r : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    upperCharacterMeasurableEquiv rho r chi = upperCharacterAction rho r chi :=
  rfl

end

end IntegralGeneratorShearSelector
end GroupApproximation
