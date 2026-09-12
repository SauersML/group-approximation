import GroupApproximation.PropertyT.IntegralColumnPlaneSpectralMassBound

/-!
# Generator-shear valuation descent for the integral column plane

`IntegralColumnPlaneSpectralMassBound` classifies a Gelfand character of the
represented column plane by the pair of least word degrees at which it is
visible in the two root coordinates, and analyses how that classification
moves under the two *unit* shears `x₀₁(1)` and `x₁₀(1)`.  Multiplication by
`1` cannot lower a word degree, so the unit shears never move a character
downward, and the resulting placement statements are too weak to bound any
mass: `columnPlaneSpectralMeasure_A_union_B_le_ABC` has its own left side on
its right side.

This file supplies the missing half: the *generator* shears `x₀₁(ι x)` and
`x₁₀(ι x)`, which do lower a word degree, by exactly one.  The estimate the
characteristic-`p` route runs on the same regions
(`FreeRootPlaneMass.sum_planeMass_AB_le_coarse_CD` and
`sum_planeMass_CB_le_coarse_AD`) is driven precisely by this descent, and the
descent is characteristic-free:

* if a character is trivial on every word of degree `< v` and nontrivial on
  some word `w` of degree `v ≥ 1`, then writing `w = x · w'` exhibits an
  alphabet letter `x` for which the coefficient family `ι x * ·` is nontrivial
  at degree `v - 1` and trivial below it;
* a strictly earlier term cannot be cancelled by a strictly later one, since
  at the earlier degree the later summand is still trivial.

Both facts are proved here for `ℤ⟨X⟩`, with no finiteness, characteristic or
literature hypothesis, and combined into the two placement theorems

* `wordPairRegion_lowerGenerator_eq_C_or_D` — a character of region `A` or `B`
  at one stage lands in region `C` or `D` one stage down, under the lower
  generator shear selected by the descent;
* `wordPairRegion_upperGenerator_eq_A_or_D` — the mirror statement for region
  `C` or `B` under the upper generator shear.

Nothing here assumes `ColumnPlaneMassBound`, and nothing here is a measure
statement: these are exact pointwise placements, which is what a mass
comparison consumes.
-/

namespace GroupApproximation
namespace IntegralGeneratorShearDescent

open Set WeakDual
open IntegralCharacterMass
open IntegralColumnPlaneSpectralMeasure
open IntegralColumnPlaneSpectralShear
open IntegralColumnPlaneSpectralTorus
open IntegralColumnPlaneSpectralMassBound
open FreeAlgebraDegree

noncomputable section

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {X : Type u} [Fintype X]
variable (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))

/-! ### The dual action of a shear with an arbitrary coefficient -/

/-- The dual action of the lower shear `x₁₀(r)` with an arbitrary coefficient.
The unit case is `IntegralColumnPlaneSpectralMassBound.lowerUnitCharacterAction`. -/
def lowerCharacterAction (r : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    characterSpace ℂ (representedColumnPlane rho).algebra :=
  CommutativeCStarCovariance.characterAction (representedColumnPlane rho).algebra
    ((representedColumnPlane rho).rho (lowerShear r))
    (lowerShear_forward rho r) (lowerShear_backward rho r) chi

/-- The dual action of the upper shear `x₀₁(r)` with an arbitrary coefficient. -/
def upperCharacterAction (r : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    characterSpace ℂ (representedColumnPlane rho).algebra :=
  CommutativeCStarCovariance.characterAction (representedColumnPlane rho).algebra
    ((representedColumnPlane rho).rho (upperShear r))
    (upperShear_forward rho r) (upperShear_backward rho r) chi

omit [Fintype X] in
theorem coordinateAngle_lowerCharacterAction_one (r a : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    coordinateAngle rho (1, a) (lowerCharacterAction rho r chi) =
      coordinateAngle rho (1, a) chi :=
  coordinateAngle_characterAction_lower_one rho r a chi

omit [Fintype X] in
theorem coordinateAngle_lowerCharacterAction_zero (r a : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    coordinateAngle rho (0, a) (lowerCharacterAction rho r chi) =
      coordinateAngle rho (1, r * a) chi + coordinateAngle rho (0, a) chi :=
  coordinateAngle_characterAction_lower_zero rho r a chi

omit [Fintype X] in
theorem coordinateAngle_upperCharacterAction_zero (r a : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    coordinateAngle rho (0, a) (upperCharacterAction rho r chi) =
      coordinateAngle rho (0, a) chi :=
  coordinateAngle_characterAction_upper_zero rho r a chi

omit [Fintype X] in
theorem coordinateAngle_upperCharacterAction_one (r a : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    coordinateAngle rho (1, a) (upperCharacterAction rho r chi) =
      coordinateAngle rho (0, r * a) chi + coordinateAngle rho (1, a) chi :=
  coordinateAngle_characterAction_upper_one rho r a chi

/-! ### Reading the least visible degree off single words -/

/-- The least visible degree is attained by a word of exactly that length. -/
theorem exists_word_freeWordLength_eq_degreeWithin
    (b : Fin 2) (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho b n) :
    ∃ w : FreeMonoid X,
      freeWordLength X w = leastRootWordDegreeWithin rho b n chi ∧
      coordinateAngle rho (b, wordMonomial X ℤ w) chi ≠ 0 := by
  obtain ⟨w, hw, hne⟩ :=
    (mem_rootWordVisibleSet_iff rho b _ chi).mp
      (leastRootWordDegreeWithin_mem rho b n chi hvis)
  refine ⟨w, ?_, hne⟩
  rcases lt_or_eq_of_le hw with hlt | heq
  · exact absurd
      ((mem_rootWordVisibleSet_iff rho b _ chi).mpr ⟨w, le_rfl, hne⟩)
      (not_mem_rootWordVisibleSet_of_lt_degreeWithin rho b n chi hlt)
  · exact heq

/-- Below the least visible degree every word coordinate is trivial. -/
theorem coordinateAngle_eq_zero_of_lt_degreeWithin
    (b : Fin 2) (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    {w : FreeMonoid X}
    (hw : freeWordLength X w < leastRootWordDegreeWithin rho b n chi) :
    coordinateAngle rho (b, wordMonomial X ℤ w) chi = 0 := by
  by_contra hne
  exact (not_mem_rootWordVisibleSet_of_lt_degreeWithin rho b n chi hw)
    ((mem_rootWordVisibleSet_iff rho b _ chi).mpr ⟨w, le_rfl, hne⟩)

/-- A visible degree that is minimal identifies the selector at any larger
stage. -/
theorem leastRootWordDegreeWithin_eq_of_visible_of_min
    (b : Fin 2) (m d : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hd : d ≤ m) (hvis : chi ∈ rootWordVisibleSet rho b d)
    (hmin : ∀ e, e < d → chi ∉ rootWordVisibleSet rho b e) :
    leastRootWordDegreeWithin rho b m chi = d := by
  have hvism : chi ∈ rootWordVisibleSet rho b m :=
    rootWordVisibleSet_mono rho b hd hvis
  have hle : leastRootWordDegreeWithin rho b m chi ≤ d := by
    by_contra hlt
    exact (not_mem_rootWordVisibleSet_of_lt_degreeWithin rho b m chi
      (by omega)) hvis
  have hge : d ≤ leastRootWordDegreeWithin rho b m chi := by
    by_contra hlt
    exact hmin _ (by omega)
      (leastRootWordDegreeWithin_mem rho b m chi hvism)
  omega

/-- The selector does not depend on the stage, as long as the stage is large
enough to see it. -/
theorem leastRootWordDegreeWithin_stage_eq
    (b : Fin 2) (n m : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho b n)
    (hle : leastRootWordDegreeWithin rho b n chi ≤ m) :
    leastRootWordDegreeWithin rho b m chi =
      leastRootWordDegreeWithin rho b n chi := by
  refine leastRootWordDegreeWithin_eq_of_visible_of_min rho b m _ chi hle
    (leastRootWordDegreeWithin_mem rho b n chi hvis) ?_
  intro e he
  exact not_mem_rootWordVisibleSet_of_lt_degreeWithin rho b n chi he

/-! ### The descent -/

/-- **Valuation descent.**  A character first visible in coordinate `b` at a
positive degree `v` has an alphabet letter `x` for which the shifted
coefficient family `ι x * ·` is nontrivial already at degree `v - 1`.  The
letter is the first letter of any shortest detecting word. -/
theorem exists_generator_descent
    (b : Fin 2) (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho b n)
    (hpos : 0 < leastRootWordDegreeWithin rho b n chi) :
    ∃ x : X, ∃ w : FreeMonoid X,
      freeWordLength X w + 1 = leastRootWordDegreeWithin rho b n chi ∧
      coordinateAngle rho (b, FreeAlgebra.ι ℤ x * wordMonomial X ℤ w) chi ≠ 0 := by
  obtain ⟨w0, hlen, hne⟩ :=
    exists_word_freeWordLength_eq_degreeWithin rho b n chi hvis
  obtain ⟨x, w, hword, hmono⟩ :=
    wordMonomial_eq_generator_mul_of_freeWordLength_pos X ℤ w0 (by omega)
  refine ⟨x, w, ?_, ?_⟩
  · have hlift := congrArg (freeWordLength X) hword
    rw [freeWordLength_mul, freeWordLength_of] at hlift
    omega
  · rw [← hmono]
    exact hne

/-- The shifted coefficient family is trivial strictly below the descended
degree, for every letter. -/
theorem coordinateAngle_generator_mul_eq_zero_of_succ_lt_degreeWithin
    (b : Fin 2) (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (x : X) {w : FreeMonoid X}
    (hw : freeWordLength X w + 1 < leastRootWordDegreeWithin rho b n chi) :
    coordinateAngle rho (b, FreeAlgebra.ι ℤ x * wordMonomial X ℤ w) chi = 0 := by
  have hmul : FreeAlgebra.ι ℤ x * wordMonomial X ℤ w =
      wordMonomial X ℤ (FreeMonoid.of x * w) := by
    rw [← wordMonomial_of X ℤ x, wordMonomial_mul]
  rw [hmul]
  refine coordinateAngle_eq_zero_of_lt_degreeWithin rho b n chi ?_
  rw [freeWordLength_mul, freeWordLength_of]
  omega

/-! ### Placement of the lower generator shear -/

/-- The lower shear leaves the second root coordinate untouched. -/
theorem rootWordVisibleSet_lowerCharacterAction_one_iff
    (r : FreeAlgebra ℤ X) (d : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    lowerCharacterAction rho r chi ∈ rootWordVisibleSet rho 1 d ↔
      chi ∈ rootWordVisibleSet rho 1 d := by
  rw [mem_rootWordVisibleSet_iff, mem_rootWordVisibleSet_iff]
  constructor
  · rintro ⟨w, hw, hne⟩
    exact ⟨w, hw, by rwa [coordinateAngle_lowerCharacterAction_one] at hne⟩
  · rintro ⟨w, hw, hne⟩
    exact ⟨w, hw, by rwa [coordinateAngle_lowerCharacterAction_one]⟩

theorem leastRootWordDegreeWithin_lowerCharacterAction_one
    (r : FreeAlgebra ℤ X) (m : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    leastRootWordDegreeWithin rho 1 m (lowerCharacterAction rho r chi) =
      leastRootWordDegreeWithin rho 1 m chi :=
  leastRootWordDegreeWithin_eq_of_visible_iff rho 1 m chi _
    (fun d ↦ rootWordVisibleSet_lowerCharacterAction_one_iff rho r d chi)

/-- **The lower generator shear pushes the second-coordinate valuation one
degree down into the first coordinate.**  The hypothesis `hle` is what rules
out cancellation: the first coordinate is still trivial at the descended
degree. -/
theorem leastRootWordDegreeWithin_lowerGenerator_zero
    (n m : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (x : X) {w : FreeMonoid X}
    (hlen : freeWordLength X w + 1 = leastRootWordDegreeWithin rho 1 n chi)
    (hne : coordinateAngle rho
      (1, FreeAlgebra.ι ℤ x * wordMonomial X ℤ w) chi ≠ 0)
    (hle : leastRootWordDegreeWithin rho 1 n chi ≤
      leastRootWordDegreeWithin rho 0 n chi)
    (hstage : leastRootWordDegreeWithin rho 1 n chi ≤ m + 1) :
    leastRootWordDegreeWithin rho 0 m
        (lowerCharacterAction rho (FreeAlgebra.ι ℤ x) chi) =
      leastRootWordDegreeWithin rho 1 n chi - 1 := by
  have hvisible : lowerCharacterAction rho (FreeAlgebra.ι ℤ x) chi ∈
      rootWordVisibleSet rho 0 (freeWordLength X w) := by
    refine (mem_rootWordVisibleSet_iff rho 0 _ _).mpr ⟨w, le_rfl, ?_⟩
    rw [coordinateAngle_lowerCharacterAction_zero,
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 0 n chi (by omega),
      add_zero]
    exact hne
  have hmin : ∀ e, e < freeWordLength X w →
      lowerCharacterAction rho (FreeAlgebra.ι ℤ x) chi ∉
        rootWordVisibleSet rho 0 e := by
    intro e he hmem
    obtain ⟨u, hu, hune⟩ := (mem_rootWordVisibleSet_iff rho 0 e _).mp hmem
    apply hune
    rw [coordinateAngle_lowerCharacterAction_zero,
      coordinateAngle_generator_mul_eq_zero_of_succ_lt_degreeWithin
        rho 1 n chi x (by omega),
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 0 n chi (by omega),
      add_zero]
  have hstep := leastRootWordDegreeWithin_eq_of_visible_of_min rho 0 m
    (freeWordLength X w) _ (by omega) hvisible hmin
  omega

/-- **Placement of region `A ∪ B` under the selected lower generator shear.**
A character whose second-coordinate valuation is positive, no larger than its
first, and interior to the stage, is carried one stage down into region `C`,
or into region `D` when the descended degree is zero. -/
theorem wordPairRegion_lowerGenerator_eq_C_or_D
    (n m : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho 1 n)
    (hpos : 0 < leastRootWordDegreeWithin rho 1 n chi)
    (hle : leastRootWordDegreeWithin rho 1 n chi ≤
      leastRootWordDegreeWithin rho 0 n chi)
    (hstage : leastRootWordDegreeWithin rho 1 n chi ≤ m) :
    ∃ x : X,
      wordPairRegion rho m (lowerCharacterAction rho (FreeAlgebra.ι ℤ x) chi)
          = .C ∨
      wordPairRegion rho m (lowerCharacterAction rho (FreeAlgebra.ι ℤ x) chi)
          = .D := by
  obtain ⟨x, w, hlen, hne⟩ := exists_generator_descent rho 1 n chi hvis hpos
  refine ⟨x, ?_⟩
  have hzero := leastRootWordDegreeWithin_lowerGenerator_zero rho n m chi x
    hlen hne hle (by omega)
  have hone :
      leastRootWordDegreeWithin rho 1 m
          (lowerCharacterAction rho (FreeAlgebra.ι ℤ x) chi) =
        leastRootWordDegreeWithin rho 1 n chi := by
    rw [leastRootWordDegreeWithin_lowerCharacterAction_one]
    exact leastRootWordDegreeWithin_stage_eq rho 1 n m chi hvis hstage
  rw [wordPairRegion, hzero, hone]
  rcases Nat.eq_zero_or_pos (leastRootWordDegreeWithin rho 1 n chi - 1) with
    h0 | hp
  · right
    exact wordPairRegionOfDegrees_eq_D_of_left_zero m _ _ h0
  · left
    exact wordPairRegionOfDegrees_eq_C_of_pos_of_lt m _ _ (by omega) (by omega)

/-! ### Placement of the upper generator shear -/

/-- The upper shear leaves the first root coordinate untouched. -/
theorem rootWordVisibleSet_upperCharacterAction_zero_iff
    (r : FreeAlgebra ℤ X) (d : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    upperCharacterAction rho r chi ∈ rootWordVisibleSet rho 0 d ↔
      chi ∈ rootWordVisibleSet rho 0 d := by
  rw [mem_rootWordVisibleSet_iff, mem_rootWordVisibleSet_iff]
  constructor
  · rintro ⟨w, hw, hne⟩
    exact ⟨w, hw, by rwa [coordinateAngle_upperCharacterAction_zero] at hne⟩
  · rintro ⟨w, hw, hne⟩
    exact ⟨w, hw, by rwa [coordinateAngle_upperCharacterAction_zero]⟩

theorem leastRootWordDegreeWithin_upperCharacterAction_zero
    (r : FreeAlgebra ℤ X) (m : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    leastRootWordDegreeWithin rho 0 m (upperCharacterAction rho r chi) =
      leastRootWordDegreeWithin rho 0 m chi :=
  leastRootWordDegreeWithin_eq_of_visible_iff rho 0 m chi _
    (fun d ↦ rootWordVisibleSet_upperCharacterAction_zero_iff rho r d chi)

/-- The mirror of `leastRootWordDegreeWithin_lowerGenerator_zero`. -/
theorem leastRootWordDegreeWithin_upperGenerator_one
    (n m : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (x : X) {w : FreeMonoid X}
    (hlen : freeWordLength X w + 1 = leastRootWordDegreeWithin rho 0 n chi)
    (hne : coordinateAngle rho
      (0, FreeAlgebra.ι ℤ x * wordMonomial X ℤ w) chi ≠ 0)
    (hle : leastRootWordDegreeWithin rho 0 n chi ≤
      leastRootWordDegreeWithin rho 1 n chi)
    (hstage : leastRootWordDegreeWithin rho 0 n chi ≤ m + 1) :
    leastRootWordDegreeWithin rho 1 m
        (upperCharacterAction rho (FreeAlgebra.ι ℤ x) chi) =
      leastRootWordDegreeWithin rho 0 n chi - 1 := by
  have hvisible : upperCharacterAction rho (FreeAlgebra.ι ℤ x) chi ∈
      rootWordVisibleSet rho 1 (freeWordLength X w) := by
    refine (mem_rootWordVisibleSet_iff rho 1 _ _).mpr ⟨w, le_rfl, ?_⟩
    rw [coordinateAngle_upperCharacterAction_one,
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 1 n chi (by omega),
      add_zero]
    exact hne
  have hmin : ∀ e, e < freeWordLength X w →
      upperCharacterAction rho (FreeAlgebra.ι ℤ x) chi ∉
        rootWordVisibleSet rho 1 e := by
    intro e he hmem
    obtain ⟨u, hu, hune⟩ := (mem_rootWordVisibleSet_iff rho 1 e _).mp hmem
    apply hune
    rw [coordinateAngle_upperCharacterAction_one,
      coordinateAngle_generator_mul_eq_zero_of_succ_lt_degreeWithin
        rho 0 n chi x (by omega),
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 1 n chi (by omega),
      add_zero]
  have hstep := leastRootWordDegreeWithin_eq_of_visible_of_min rho 1 m
    (freeWordLength X w) _ (by omega) hvisible hmin
  omega

/-- **Placement of region `C ∪ B` under the selected upper generator shear.** -/
theorem wordPairRegion_upperGenerator_eq_A_or_D
    (n m : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho 0 n)
    (hpos : 0 < leastRootWordDegreeWithin rho 0 n chi)
    (hle : leastRootWordDegreeWithin rho 0 n chi ≤
      leastRootWordDegreeWithin rho 1 n chi)
    (hstage : leastRootWordDegreeWithin rho 0 n chi ≤ m) :
    ∃ x : X,
      wordPairRegion rho m (upperCharacterAction rho (FreeAlgebra.ι ℤ x) chi)
          = .A ∨
      wordPairRegion rho m (upperCharacterAction rho (FreeAlgebra.ι ℤ x) chi)
          = .D := by
  obtain ⟨x, w, hlen, hne⟩ := exists_generator_descent rho 0 n chi hvis hpos
  refine ⟨x, ?_⟩
  have hone := leastRootWordDegreeWithin_upperGenerator_one rho n m chi x
    hlen hne hle (by omega)
  have hzero :
      leastRootWordDegreeWithin rho 0 m
          (upperCharacterAction rho (FreeAlgebra.ι ℤ x) chi) =
        leastRootWordDegreeWithin rho 0 n chi := by
    rw [leastRootWordDegreeWithin_upperCharacterAction_zero]
    exact leastRootWordDegreeWithin_stage_eq rho 0 n m chi hvis hstage
  rw [wordPairRegion, hzero, hone]
  rcases Nat.eq_zero_or_pos (leastRootWordDegreeWithin rho 0 n chi - 1) with
    h0 | hp
  · right
    exact wordPairRegionOfDegrees_eq_D_of_right_zero m _ _ h0
  · left
    exact wordPairRegionOfDegrees_eq_A_of_pos_of_lt m _ _ (by omega) (by omega)

/-! ### Placement of the unit shears: `A → B` and `C → B`

The generator shears above move a character one degree down; the unit shears
move nothing, but they *fold* the two off-diagonal regions onto the diagonal
one.  These two placements are what makes the endgame arithmetic close: with
`A ≤ B`, `C ≤ B`, `2B ≤ 2D` and the torus bound on `D`, the total nontrivial
mass is bounded by `4D` plus the shear errors.  They are the integral
analogues of `FreeRootPlaneMassBase.sum_planeMass_A_le_sum_B` and
`sum_planeMass_C_le_sum_B`. -/

omit [Fintype X] in
theorem lowerCharacterAction_one_eq
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    lowerCharacterAction rho 1 chi = lowerUnitCharacterAction rho chi :=
  rfl

omit [Fintype X] in
theorem upperCharacterAction_one_eq
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    upperCharacterAction rho 1 chi = upperUnitCharacterAction rho chi :=
  rfl

/-- **No cancellation when the copied term is the earlier one.**  If the
second-coordinate valuation is strictly the smaller, the lower unit shear
copies it into the first coordinate unchanged. -/
theorem leastRootWordDegreeWithin_lowerUnit_zero_of_gt
    (n : ℕ) (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho 1 n)
    (hlt : leastRootWordDegreeWithin rho 1 n chi <
      leastRootWordDegreeWithin rho 0 n chi) :
    leastRootWordDegreeWithin rho 0 n (lowerUnitCharacterAction rho chi) =
      leastRootWordDegreeWithin rho 1 n chi := by
  obtain ⟨w, hlen, hne⟩ :=
    exists_word_freeWordLength_eq_degreeWithin rho 1 n chi hvis
  have hvisible : lowerUnitCharacterAction rho chi ∈
      rootWordVisibleSet rho 0 (freeWordLength X w) := by
    refine (mem_rootWordVisibleSet_iff rho 0 _ _).mpr ⟨w, le_rfl, ?_⟩
    rw [← lowerCharacterAction_one_eq,
      coordinateAngle_lowerCharacterAction_zero, one_mul,
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 0 n chi (by omega),
      add_zero]
    exact hne
  have hmin : ∀ e, e < freeWordLength X w →
      lowerUnitCharacterAction rho chi ∉ rootWordVisibleSet rho 0 e := by
    intro e he hmem
    obtain ⟨u, hu, hune⟩ := (mem_rootWordVisibleSet_iff rho 0 e _).mp hmem
    apply hune
    rw [← lowerCharacterAction_one_eq,
      coordinateAngle_lowerCharacterAction_zero, one_mul,
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 1 n chi (by omega),
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 0 n chi (by omega),
      add_zero]
  have hstage : freeWordLength X w ≤ n := by
    have hale := leastRootWordDegreeWithin_le_succ rho 0 n chi
    omega
  have hstep := leastRootWordDegreeWithin_eq_of_visible_of_min rho 0 n
    (freeWordLength X w) _ hstage hvisible hmin
  omega

/-- The mirror statement for the upper unit shear. -/
theorem leastRootWordDegreeWithin_upperUnit_one_of_gt
    (n : ℕ) (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho 0 n)
    (hlt : leastRootWordDegreeWithin rho 0 n chi <
      leastRootWordDegreeWithin rho 1 n chi) :
    leastRootWordDegreeWithin rho 1 n (upperUnitCharacterAction rho chi) =
      leastRootWordDegreeWithin rho 0 n chi := by
  obtain ⟨w, hlen, hne⟩ :=
    exists_word_freeWordLength_eq_degreeWithin rho 0 n chi hvis
  have hvisible : upperUnitCharacterAction rho chi ∈
      rootWordVisibleSet rho 1 (freeWordLength X w) := by
    refine (mem_rootWordVisibleSet_iff rho 1 _ _).mpr ⟨w, le_rfl, ?_⟩
    rw [← upperCharacterAction_one_eq,
      coordinateAngle_upperCharacterAction_one, one_mul,
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 1 n chi (by omega),
      add_zero]
    exact hne
  have hmin : ∀ e, e < freeWordLength X w →
      upperUnitCharacterAction rho chi ∉ rootWordVisibleSet rho 1 e := by
    intro e he hmem
    obtain ⟨u, hu, hune⟩ := (mem_rootWordVisibleSet_iff rho 1 e _).mp hmem
    apply hune
    rw [← upperCharacterAction_one_eq,
      coordinateAngle_upperCharacterAction_one, one_mul,
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 0 n chi (by omega),
      coordinateAngle_eq_zero_of_lt_degreeWithin rho 1 n chi (by omega),
      add_zero]
  have hstage : freeWordLength X w ≤ n := by
    have hble := leastRootWordDegreeWithin_le_succ rho 1 n chi
    omega
  have hstep := leastRootWordDegreeWithin_eq_of_visible_of_min rho 1 n
    (freeWordLength X w) _ hstage hvisible hmin
  omega

/-- **Region `A` folds onto region `B` under the lower unit shear.** -/
theorem wordPairRegion_lowerUnit_eq_B_of_eq_A
    (n : ℕ) (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hregion : wordPairRegion rho n chi = .A) :
    wordPairRegion rho n (lowerUnitCharacterAction rho chi) = .B := by
  rw [wordPairRegion] at hregion
  obtain ⟨ha, hb, hlt⟩ := wordPairRegionOfDegrees_A_data n _ _ hregion
  have hale := leastRootWordDegreeWithin_le_succ rho 0 n chi
  have hble : leastRootWordDegreeWithin rho 1 n chi ≤ n := by omega
  have hvis : chi ∈ rootWordVisibleSet rho 1 n := by
    by_contra hnot
    have hsentinel :=
      leastRootWordDegreeWithin_eq_succ_of_not_mem rho 1 n chi hnot
    omega
  have hzero := leastRootWordDegreeWithin_lowerUnit_zero_of_gt rho n chi
    hvis (by omega)
  have hone := leastRootWordDegreeWithin_lowerUnit_one rho n chi
  rw [wordPairRegion, hzero, hone]
  exact wordPairRegionOfDegrees_eq_B_of_pos_of_eq_of_le n _ _ hb rfl hble

/-- **Region `C` folds onto region `B` under the upper unit shear.** -/
theorem wordPairRegion_upperUnit_eq_B_of_eq_C
    (n : ℕ) (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hregion : wordPairRegion rho n chi = .C) :
    wordPairRegion rho n (upperUnitCharacterAction rho chi) = .B := by
  rw [wordPairRegion] at hregion
  obtain ⟨ha, hb, hlt⟩ := wordPairRegionOfDegrees_C_data n _ _ hregion
  have hble := leastRootWordDegreeWithin_le_succ rho 1 n chi
  have hale : leastRootWordDegreeWithin rho 0 n chi ≤ n := by omega
  have hvis : chi ∈ rootWordVisibleSet rho 0 n := by
    by_contra hnot
    have hsentinel :=
      leastRootWordDegreeWithin_eq_succ_of_not_mem rho 0 n chi hnot
    omega
  have hone := leastRootWordDegreeWithin_upperUnit_one_of_gt rho n chi
    hvis (by omega)
  have hzero := leastRootWordDegreeWithin_upperUnit_zero rho n chi
  rw [wordPairRegion, hzero, hone]
  exact wordPairRegionOfDegrees_eq_B_of_pos_of_eq_of_le n _ _ ha rfl hale

/-! ### Region `D` is exactly the unit-detected part of the spectrum -/

/-- A root coordinate has least visible degree zero exactly when the
character is nontrivial at the unit coefficient of that root. -/
theorem leastRootWordDegreeWithin_eq_zero_iff
    (b : Fin 2) (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    leastRootWordDegreeWithin rho b n chi = 0 ↔
      chi ((representedColumnPlane rho).coordinate (b, 1)) ≠ 1 := by
  have hzeroVisible : chi ∈ rootWordVisibleSet rho b 0 ↔
      chi ((representedColumnPlane rho).coordinate (b, 1)) ≠ 1 := by
    rw [mem_rootWordVisibleSet_iff]
    constructor
    · rintro ⟨w, hw, hne⟩
      have hw1 : w = 1 := (freeWordLength_eq_zero_iff X w).mp (by omega)
      subst hw1
      rw [wordMonomial_one] at hne
      exact fun hone ↦ hne ((coordinateAngle_eq_zero_iff rho (b, 1) chi).mpr hone)
    · intro hne
      refine ⟨1, by simp [freeWordLength_eq_zero_iff], ?_⟩
      rw [wordMonomial_one]
      exact fun hzero ↦ hne ((coordinateAngle_eq_zero_iff rho (b, 1) chi).mp hzero)
  constructor
  · intro hzero
    refine hzeroVisible.mp ?_
    have hvis : chi ∈ rootWordVisibleSet rho b n := by
      by_contra hnot
      rw [leastRootWordDegreeWithin_eq_succ_of_not_mem rho b n chi hnot] at hzero
      omega
    have := leastRootWordDegreeWithin_mem rho b n chi hvis
    rwa [hzero] at this
  · intro hne
    have hvis0 : chi ∈ rootWordVisibleSet rho b 0 := hzeroVisible.mpr hne
    exact leastRootWordDegreeWithin_eq_of_visible_of_min rho b n 0 chi
      (Nat.zero_le n) hvis0 (fun e he ↦ absurd he (Nat.not_lt_zero e))

/-- **Region `D` does not depend on the stage: it is the part of the
spectrum the two unit column roots already detect.**  Consequently the
already-proved scalar torus estimate
`IntegralColumnPlaneSpectralMassBound.scalarTorusMeasure_punctured_mass_le`
bounds its mass. -/
theorem wordPairRegionSet_D_eq_unitRootNontrivialSet (n : ℕ) :
    wordPairRegionSet rho n .D = unitRootNontrivialSet rho := by
  ext chi
  constructor
  · intro hchi
    have hdata := wordPairRegionOfDegrees_D_data n _ _ hchi
    rcases hdata with h0 | h1
    · exact Or.inl ((leastRootWordDegreeWithin_eq_zero_iff rho 0 n chi).mp h0)
    · exact Or.inr ((leastRootWordDegreeWithin_eq_zero_iff rho 1 n chi).mp h1)
  · intro hchi
    change wordPairRegionOfDegrees n _ _ = _
    rcases hchi with h0 | h1
    · exact wordPairRegionOfDegrees_eq_D_of_left_zero n _ _
        ((leastRootWordDegreeWithin_eq_zero_iff rho 0 n chi).mpr h0)
    · exact wordPairRegionOfDegrees_eq_D_of_right_zero n _ _
        ((leastRootWordDegreeWithin_eq_zero_iff rho 1 n chi).mpr h1)

end

end IntegralGeneratorShearDescent
end GroupApproximation
