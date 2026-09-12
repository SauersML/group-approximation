import GroupApproximation.PropertyT.IntegralGeneratorShearDescentMass

/-!
# Word monomials span every coefficient a character can see

The `A/B/C/D` classification of `IntegralColumnPlaneSpectralMassBound` measures
a character only on *word monomial* coefficients.  To turn a bound on the
regions into a bound on the displacement by an arbitrary coefficient one needs
the converse direction: a character trivial on every word monomial of degree at
most `n` is trivial on the whole degree-`n` stage.

That is proved here.  Evaluation of a Gelfand character at the column
coordinates is an additive character of the coefficient ring, because the
elementary root map is additive in its coefficient and the character is
multiplicative.  A degree stage is spanned over `ℤ` by its word monomials, so
an additive character killing all of them kills the stage.

The consequence packaged at the end is the set inclusion the endgame uses: for
a coefficient in the degree-`n` stage, the characters that detect it all lie in
one of the four nonzero regions at stage `n`.
-/

namespace GroupApproximation
namespace IntegralColumnPlaneSpanning

open Set MeasureTheory WeakDual
open IntegralCharacterMass
open IntegralColumnPlaneSpectralMeasure
open IntegralColumnPlaneSpectralTorus
open IntegralColumnPlaneSpectralMassBound
open FreeAlgebraDegree

noncomputable section

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {X : Type u} [Fintype X]
variable (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))

noncomputable local instance columnPlaneCharacterMeasurableSpaceSpan :
    MeasurableSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  borel _

local instance columnPlaneCharacterBorelSpaceSpan :
    BorelSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  ⟨rfl⟩

/-! ### The coefficient character -/

omit [Fintype X] in
/-- The column coordinate is additive in its coefficient. -/
theorem coordinate_add (b : Fin 2) (a a' : FreeAlgebra ℤ X) :
    (representedColumnPlane rho).coordinate ((b, a + a')) =
      (representedColumnPlane rho).coordinate ((b, a)) *
        (representedColumnPlane rho).coordinate ((b, a')) := by
  apply Subtype.ext
  change ((((representedColumnPlane rho).rho (columnRoot (b, a + a')) :
      unitary (Complexification E →L[ℂ] Complexification E)) :
        Complexification E →L[ℂ] Complexification E)) =
    ((((representedColumnPlane rho).rho (columnRoot (b, a)) :
      unitary (Complexification E →L[ℂ] Complexification E)) :
        Complexification E →L[ℂ] Complexification E) *
      (((representedColumnPlane rho).rho (columnRoot (b, a')) :
        unitary (Complexification E →L[ℂ] Complexification E)) :
          Complexification E →L[ℂ] Complexification E))
  have hroot : columnRoot ((b, a + a') : Fin 2 × FreeAlgebra ℤ X) =
      columnRoot ((b, a) : Fin 2 × FreeAlgebra ℤ X) *
        columnRoot ((b, a') : Fin 2 × FreeAlgebra ℤ X) :=
    (elementaryRoot_mul (columnSource b) 2
      (columnSource_ne_terminal b) a a').symm
  rw [hroot, map_mul]
  rfl

omit [Fintype X] in
/-- The zero coefficient gives the identity coordinate. -/
theorem coordinate_zero (b : Fin 2) :
    (representedColumnPlane rho).coordinate ((b, (0 : FreeAlgebra ℤ X))) = 1 := by
  apply Subtype.ext
  change ((((representedColumnPlane rho).rho
      (columnRoot (b, (0 : FreeAlgebra ℤ X))) :
      unitary (Complexification E →L[ℂ] Complexification E)) :
        Complexification E →L[ℂ] Complexification E)) = 1
  have hroot : columnRoot ((b, (0 : FreeAlgebra ℤ X)) :
      Fin 2 × FreeAlgebra ℤ X) = 1 := by
    simp [columnRoot]
  rw [hroot, map_one]
  rfl

omit [Fintype X] in
theorem coordinateAngle_add (b : Fin 2) (a a' : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    coordinateAngle rho ((b, a + a')) chi =
      coordinateAngle rho ((b, a)) chi + coordinateAngle rho ((b, a')) chi := by
  apply AddCircle.injective_toCircle (by norm_num)
  rw [coordinateAngle_toCircle, AddCircle.toCircle_add,
    coordinateAngle_toCircle, coordinateAngle_toCircle]
  apply Circle.ext
  change chi ((representedColumnPlane rho).coordinate ((b, a + a'))) =
    chi ((representedColumnPlane rho).coordinate ((b, a))) *
      chi ((representedColumnPlane rho).coordinate ((b, a')))
  rw [coordinate_add, map_mul]

omit [Fintype X] in
theorem coordinateAngle_zero (b : Fin 2)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    coordinateAngle rho ((b, (0 : FreeAlgebra ℤ X))) chi = 0 := by
  apply (coordinateAngle_eq_zero_iff rho _ chi).mpr
  rw [coordinate_zero, map_one]

/-- Evaluation of a fixed character at one column root, as an additive
character of the coefficient ring. -/
def coordinateAngleHom (b : Fin 2)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    FreeAlgebra ℤ X →+ AddCircle (1 : ℝ) where
  toFun a := coordinateAngle rho ((b, a)) chi
  map_zero' := coordinateAngle_zero rho b chi
  map_add' a a' := coordinateAngle_add rho b a a' chi

omit [Fintype X] in
@[simp] theorem coordinateAngleHom_apply (b : Fin 2)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (a : FreeAlgebra ℤ X) :
    coordinateAngleHom rho b chi a = coordinateAngle rho ((b, a)) chi :=
  rfl

/-! ### Word monomials span a degree stage -/

/-- **A character trivial on every word monomial of degree at most `n` is
trivial on the whole degree-`n` stage.** -/
theorem coordinateAngle_eq_zero_of_mem_degreeLE (b : Fin 2)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (n : ℕ) (a : FreeAlgebra ℤ X) (ha : a ∈ degreeLE X ℤ n)
    (hzero : ∀ w : FreeMonoid X, freeWordLength X w ≤ n →
      coordinateAngle rho ((b, wordMonomial X ℤ w)) chi = 0) :
    coordinateAngle rho ((b, a)) chi = 0 := by
  classical
  have hsupport := (mem_degreeLE_iff X ℤ a n).mp ha
  have hsum := eq_sum_support_smul_wordMonomial X ℤ a
  have hmap : coordinateAngleHom rho b chi a = 0 := by
    conv_lhs => rw [hsum]
    rw [map_sum]
    refine Finset.sum_eq_zero fun w hw ↦ ?_
    have hz : coordinateAngleHom rho b chi (wordMonomial X ℤ w) = 0 :=
      hzero w (hsupport w hw)
    exact (map_zsmul (coordinateAngleHom rho b chi)
      ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ℤ) (X := X) a).coeff w) (wordMonomial X ℤ w)).trans
      (by rw [hz]; exact smul_zero _)
  simpa using hmap

/-! ### The four nonzero regions cover every detected character -/

/-- The union of the four nonzero regions at one stage. -/
def regionUnion (n : ℕ) :
    Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  wordPairRegionSet rho n .A ∪ wordPairRegionSet rho n .B ∪
    wordPairRegionSet rho n .C ∪ wordPairRegionSet rho n .D

theorem measurableSet_regionUnion (n : ℕ) :
    MeasurableSet (regionUnion rho n) :=
  (((measurableSet_wordPairRegionSet rho n .A).union
    (measurableSet_wordPairRegionSet rho n .B)).union
      (measurableSet_wordPairRegionSet rho n .C)).union
        (measurableSet_wordPairRegionSet rho n .D)

/-- A character visible in either root coordinate at stage `n` sits in one of
the four nonzero regions. -/
theorem mem_regionUnion_of_visible (n : ℕ) (b : Fin 2)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho b n) :
    chi ∈ regionUnion rho n := by
  have hle := leastRootWordDegreeWithin_le rho b n chi hvis
  have hnotzero : wordPairRegion rho n chi ≠ .zero := by
    intro hzero
    change wordPairRegionOfDegrees n _ _ = _ at hzero
    have hsentinel : leastRootWordDegreeWithin rho 0 n chi = n + 1 ∧
        leastRootWordDegreeWithin rho 1 n chi = n + 1 := by
      by_contra hcontra
      rw [wordPairRegionOfDegrees, if_neg hcontra] at hzero
      split_ifs at hzero
    have hb : leastRootWordDegreeWithin rho b n chi = n + 1 := by
      fin_cases b
      · exact hsentinel.1
      · exact hsentinel.2
    omega
  cases hr : wordPairRegion rho n chi with
  | zero => exact absurd hr hnotzero
  | A => exact Or.inl (Or.inl (Or.inl hr))
  | B => exact Or.inl (Or.inl (Or.inr hr))
  | C => exact Or.inl (Or.inr hr)
  | D => exact Or.inr hr

/-- **The inclusion the endgame consumes.**  For a coefficient in the
degree-`n` stage, every character that detects it lies in one of the four
nonzero regions at stage `n`. -/
theorem coordinateAngle_ne_zero_subset_regionUnion (b : Fin 2) (n : ℕ)
    (a : FreeAlgebra ℤ X) (ha : a ∈ degreeLE X ℤ n) :
    {chi : characterSpace ℂ (representedColumnPlane rho).algebra |
        coordinateAngle rho ((b, a)) chi ≠ 0} ⊆ regionUnion rho n := by
  intro chi hchi
  by_contra hnot
  apply hchi
  refine coordinateAngle_eq_zero_of_mem_degreeLE rho b chi n a ha ?_
  intro w hw
  by_contra hne
  exact hnot (mem_regionUnion_of_visible rho n b chi
    ((mem_rootWordVisibleSet_iff rho b n chi).mpr ⟨w, hw, hne⟩))

end

end IntegralColumnPlaneSpanning
end GroupApproximation
