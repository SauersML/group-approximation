/-
Model tests for the definitions in the Pestov 9.1 Palomar shared block.
Fidelity driver, unwired: no lake target builds files under wip/.

Build, once the lakefile has the `PalomarPestov91Solution` library:
  lake build PalomarPestov91Solution
  lake env lean <path>/Pestov91ModelTests.lean

Every statement below is phrased in the CHALLENGE vocabulary
(`Pestov91.IsKazhdanPair`, `Pestov91.HasPropertyT`, `Pestov91.IsSoficGroup`,
`Pestov91.IsHyperlinearGroup`), which is what the Comparator compares.  The
development's controls live in the `GroupApproximation` vocabulary and reach
the challenge only through the bridges of `Palomar/Pestov91Solution.lean`.

Sources, checked against the PDFs:
* V. G. Pestov, *Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968:
  Example 2.3 (normalized Hamming distance, p. 5), Example 2.7 (normalized
  Hilbert–Schmidt metric, p. 6), Definitions 3.1–3.2 (p. 6), Theorem 3.3
  (p. 7), Theorem 3.5 (p. 8), Theorem 3.6 and Remark 3.7 (p. 9), Open question
  9.1 (p. 21).
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*:
  Definition 1.1.1 ((Q, ε)-invariant vectors), Definition 1.1.3 (Kazhdan pair,
  property (T)), Theorem 1.3.1 (a discrete group with property (T) is finitely
  generated).
-/
import Palomar.Pestov91Solution
import GroupApproximation.Kazhdan.IntegerNotKazhdan
import GroupApproximation.Kazhdan.OrbitAverageFiniteControl
import GroupApproximation.Pestov91.Centre
import GroupApproximation.Pestov91.Kazhdan
import GroupApproximation.Sofic.SoficAmplification
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace Pestov91

open GroupApproximation
open scoped Pointwise

/-! ## `IsKazhdanPair` and `HasPropertyT` -/

/-- Positive control: every finite group has property `(T)`. -/
theorem test_hasPropertyT_of_finite (G : Type) [Group G] [Finite G] : HasPropertyT G := by
  letI : Fintype G := Fintype.ofFinite G
  exact hasPropertyT_iff_hasKazhdanPropertyT.mpr SpectralGap.hasKazhdanPropertyT_of_fintype

/-- Positive control on an infinite group: `EL₃(ℤ)` has property `(T)`. -/
theorem test_hasPropertyT_intElementary : HasPropertyT ↥(elementaryGroup (Fin 3) ℤ) :=
  hasPropertyT_iff_hasKazhdanPropertyT.mpr
    GroupApproximation.Pestov91.intElementary_hasKazhdanPropertyT

/-- `EL₃(ℤ)` is infinite. -/
theorem test_infinite_intElementary : Infinite ↥(elementaryGroup (Fin 3) ℤ) :=
  elementaryGroup_infinite (R := ℤ) (0 : Fin 3) 1 (by decide)

/-- Positive control: `EL₃(ℤ)` modulo its centre is infinite and has property
`(T)`, so the conjunction `Infinite G ∧ HasPropertyT G` is satisfiable. -/
theorem test_infinite_propertyT_intElementaryModCentre :
    Infinite (↥(elementaryGroup (Fin 3) ℤ) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) ℤ)) ∧
      HasPropertyT
        (↥(elementaryGroup (Fin 3) ℤ) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) ℤ)) :=
  ⟨GroupApproximation.Pestov91.intElementaryModCentre_infinite,
    hasPropertyT_iff_hasKazhdanPropertyT.mpr
      GroupApproximation.Pestov91.intElementaryModCentre_hasKazhdanPropertyT⟩

/-- Negative control: `ℤ` does not have property `(T)`. -/
theorem test_not_hasPropertyT_int : ¬ HasPropertyT (Multiplicative ℤ) := fun h ↦
  not_hasKazhdanPropertyT_multiplicative_int (hasPropertyT_iff_hasKazhdanPropertyT.mp h)

/-- Negative control: no finite set and tolerance form a Kazhdan pair for `ℤ`. -/
theorem test_not_isKazhdanPair_int (Q : Finset (Multiplicative ℤ)) (ε : ℝ) :
    ¬ IsKazhdanPair (Multiplicative ℤ) Q ε := fun h ↦
  test_not_hasPropertyT_int ⟨Q, ε, h⟩

/-- The tolerance clause has content: a Kazhdan constant is positive
(Bekka–de la Harpe–Valette, Definition 1.1.3). -/
theorem test_not_isKazhdanPair_of_nonpos (G : Type) [Group G] (Q : Finset G) {ε : ℝ}
    (hε : ε ≤ 0) : ¬ IsKazhdanPair G Q ε := fun h ↦
  absurd h.1 (not_lt.mpr hε)

/-! ## `IsSoficGroup` and `IsHyperlinearGroup`: positive controls -/

/-- Finite groups are sofic. -/
theorem test_isSoficGroup_of_finite (G : Type) [Group G] [Finite G] : IsSoficGroup G :=
  isSoficGroup_of_isSofic (isSofic_of_finite G)

/-- The infinite cyclic group is sofic. -/
theorem test_isSoficGroup_int : IsSoficGroup (Multiplicative ℤ) :=
  isSoficGroup_of_isSofic isSofic_multiplicative_int

/-- Finite groups are hyperlinear. -/
theorem test_isHyperlinearGroup_of_finite (G : Type) [Group G] [Finite G] :
    IsHyperlinearGroup G :=
  isHyperlinearGroup_of_isHyperlinear (isHyperlinear_of_finite G)

/-- The infinite cyclic group is hyperlinear. -/
theorem test_isHyperlinearGroup_int : IsHyperlinearGroup (Multiplicative ℤ) :=
  isHyperlinearGroup_of_isSoficGroup test_isSoficGroup_int

/-! ## Degeneracy checks inside `IsSoficGroup` and `IsHyperlinearGroup` -/

/-- The sofic separation clause has content: below tolerance `1` it forces the
model to distinguish the two elements. -/
theorem test_soficSeparation_is_not_vacuous (Y : FiniteCarrier) (p q : Equiv.Perm Y)
    {ε : ℝ} (hε : ε < 1) (h : 1 - ε ≤ hammingDist Y p q) : p ≠ q := by
  intro hpq
  rw [hpq] at h
  have hzero : hammingDist Y q q = 0 := by simp [hammingDist]
  rw [hzero] at h
  linarith

/-- The hyperlinear separation clause has content: below tolerance `2` it
forces the model to distinguish the two elements. -/
theorem test_hyperlinearSeparation_is_not_vacuous (Y : FiniteCarrier) (A B : Matrix Y Y ℂ)
    {ε : ℝ} (hε : ε < 2) (h : 2 - ε ≤ hsDistSq Y A B) : A ≠ B := by
  intro hAB
  rw [hAB] at h
  have hzero : hsDistSq Y B B = 0 := by simp [hsDistSq]
  rw [hzero] at h
  linarith

/-- Below tolerance `1`, a sofic model is injective on the test set: a map that
identifies two distinct elements of `F` is never a witness. -/
theorem test_isSoficGroup_model_injOn {G : Type} [Group G] (h : IsSoficGroup G)
    (F : Finset G) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (Y : FiniteCarrier) (σ : G → Equiv.Perm Y), Set.InjOn σ (F : Set G) := by
  obtain ⟨Y, σ, -, -, hsep⟩ := h F ε hε0
  refine ⟨Y, σ, ?_⟩
  intro g hg g' hg' heq
  by_contra hne
  exact test_soficSeparation_is_not_vacuous Y (σ g) (σ g') hε1
    (hsep g (Finset.mem_coe.mp hg) g' (Finset.mem_coe.mp hg') hne) heq

/-- Below tolerance `2`, a hyperlinear model is injective on the test set. -/
theorem test_isHyperlinearGroup_model_injOn {G : Type} [Group G] (h : IsHyperlinearGroup G)
    (F : Finset G) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 2) :
    ∃ (Y : FiniteCarrier) (σ : G → Matrix Y Y ℂ), Set.InjOn σ (F : Set G) := by
  obtain ⟨Y, σ, -, -, -, hsep⟩ := h F ε hε0
  refine ⟨Y, σ, ?_⟩
  intro g hg g' hg' heq
  by_contra hne
  exact test_hyperlinearSeparation_is_not_vacuous Y (σ g) (σ g') hε1
    (hsep g (Finset.mem_coe.mp hg) g' (Finset.mem_coe.mp hg') hne) heq

/-- Pestov's condition 3.5(2), `d(σ(1), Id) ≤ ε`, follows from the block's
multiplicativity clause at `g = h = 1`, so the block loses nothing by omitting
it. -/
theorem test_identity_clause_is_implied (Y : FiniteCarrier) (p : Equiv.Perm Y)
    (ε : ℝ) (h : hammingDist Y p (p * p) ≤ ε) : hammingDist Y 1 p ≤ ε := by
  have key : hammingDist Y (p * 1) (p * p) = hammingDist Y 1 p :=
    hammingDistance_left_invariant ⟨Y.carrier, Y.fintype, Y.decidableEq⟩ p 1 p
  rw [mul_one] at key
  rw [← key]
  exact h

/-! ## Calibration of the statement: each conjunct is load-bearing -/

/-- `ℤ/2` is simple. -/
theorem test_isSimpleGroup_zmod_two : IsSimpleGroup (Multiplicative (ZMod 2)) :=
  isSimpleGroup_of_prime_card (p := 2) (Nat.card_zmod 2)

/-- Negative control for simplicity: the trivial group is not simple. -/
theorem test_not_isSimpleGroup_punit : ¬ IsSimpleGroup PUnit.{1} := fun h ↦
  not_nontrivial PUnit.{1} h.toNontrivial

/-- Dropping `Infinite` would trivialize the statement: `ℤ/2` meets every other
conjunct. -/
theorem test_finite_simple_group_meets_all_but_infinite :
    IsSimpleGroup (Multiplicative (ZMod 2)) ∧ HasPropertyT (Multiplicative (ZMod 2)) ∧
      IsSoficGroup (Multiplicative (ZMod 2)) ∧ IsHyperlinearGroup (Multiplicative (ZMod 2)) ∧
      ¬ Infinite (Multiplicative (ZMod 2)) :=
  ⟨test_isSimpleGroup_zmod_two, test_hasPropertyT_of_finite _, test_isSoficGroup_of_finite _,
    test_isHyperlinearGroup_of_finite _, not_infinite_iff_finite.mpr inferInstance⟩

/-- `ℤ` is infinite, sofic and hyperlinear, and fails property `(T)`. -/
theorem test_int_meets_infinite_sofic_hyperlinear_not_propertyT :
    Infinite (Multiplicative ℤ) ∧ IsSoficGroup (Multiplicative ℤ) ∧
      IsHyperlinearGroup (Multiplicative ℤ) ∧ ¬ HasPropertyT (Multiplicative ℤ) :=
  ⟨inferInstance, test_isSoficGroup_int, test_isHyperlinearGroup_int, test_not_hasPropertyT_int⟩

/-! ## The block's soficity is Pestov's Theorem 3.5 -/

variable {G : Type} [Group G]

/-- Pestov, Theorem 3.5, conditions (1) and (3): multiplicativity is required
only where the tested product stays in the test set, and the separation is the
fixed constant `1/4`.  Condition (2) is `test_identity_clause_is_implied`. -/
structure PestovSoficModel (G : Type) [Group G] (F : Finset G) (ε : ℝ) where
  carrier : FiniteCarrier
  nonempty : 0 < Fintype.card carrier
  map : G → Equiv.Perm carrier
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F →
    hammingDist carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    1 / 4 ≤ hammingDist carrier (map g) (map h)

/-- Soficity in the form of Pestov's Theorem 3.5. -/
def IsPestovSofic (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (PestovSoficModel G F ε)

/-- The block's soficity gives Pestov's form. -/
theorem isPestovSofic_of_isSoficGroup (h : IsSoficGroup G) : IsPestovSofic G := by
  intro F ε hε
  obtain ⟨Y, σ, hY, hmul, hsep⟩ := h F (min ε (1 / 2)) (lt_min hε (by norm_num))
  refine ⟨{ carrier := Y, nonempty := hY, map := σ,
            multiplicative := ?_, separated := ?_ }⟩
  · intro g hg h' hh' _
    exact (hmul g hg h' hh').trans (min_le_left _ _)
  · intro g hg h' hh' hne
    have hs := hsep g hg h' hh' hne
    have hm : min ε (1 / 2) ≤ 1 / 2 := min_le_right _ _
    linarith

/-- Pestov's form gives the block's soficity.  Enlarging the test set by
`F * F` removes the product restriction, and the development's tensor-power
amplification (`isSofic_of_isSoficWeak`) raises the separation from `1/4` to
`1 - ε`. -/
theorem isSoficGroup_of_isPestovSofic (h : IsPestovSofic G) : IsSoficGroup G := by
  classical
  apply isSoficGroup_of_isSofic
  refine isSofic_of_isSoficWeak (δ := 1 / 4) (by norm_num) ?_
  intro F ε hε
  obtain ⟨P⟩ := h (F ∪ F * F) ε hε
  refine ⟨{ carrier := ⟨P.carrier.carrier, P.carrier.fintype, P.carrier.decidableEq⟩
            nonempty := P.nonempty
            map := P.map
            multiplicative := ?_
            separated := ?_ }⟩
  · intro g hg h' hh'
    exact P.multiplicative g (Finset.mem_union_left _ hg) h' (Finset.mem_union_left _ hh')
      (Finset.mem_union_right F (Finset.mul_mem_mul hg hh'))
  · intro g hg h' hh' hne
    exact P.separated g (Finset.mem_union_left _ hg) h' (Finset.mem_union_left _ hh') hne

/-- **The block's soficity is Pestov's**, for every group in `Type`, countable
or not. -/
theorem isSoficGroup_iff_isPestovSofic : IsSoficGroup G ↔ IsPestovSofic G :=
  ⟨isPestovSofic_of_isSoficGroup, isSoficGroup_of_isPestovSofic⟩

/-! ## The block's hyperlinearity gives Pestov's Theorem 3.6 -/

/-- Pestov, Theorem 3.6, conditions (1) and (3), with the normalized
Hilbert–Schmidt norm of Example 2.7: `‖u - v‖₂ = √(hsDistSq Y u v)`.
Condition (2), `‖σ(1) - 1‖₂ < ε`, is left out: deriving it from the block needs
left invariance of the Hilbert–Schmidt distance under unitaries, which the
development does not have. -/
structure PestovHyperlinearModel (G : Type) [Group G] (F : Finset G) (ε : ℝ) where
  carrier : FiniteCarrier
  nonempty : 0 < Fintype.card carrier
  map : G → Matrix carrier carrier ℂ
  isUnitary : ∀ g : G, map g ∈ Matrix.unitaryGroup carrier ℂ
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F →
    Real.sqrt (hsDistSq carrier (map (g * h)) (map g * map h)) < ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    1 / 4 ≤ Real.sqrt (hsDistSq carrier (map g) (map h))

/-- Hyperlinearity in the form of Pestov's Theorem 3.6. -/
def IsPestovHyperlinear (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (PestovHyperlinearModel G F ε)

/-- The block's hyperlinearity gives conditions (1) and (3) of Pestov's
Theorem 3.6.  This checks the squaring convention of `hsDistSq`: a squared
tolerance `ε²/2` gives `‖·‖₂ < ε`, and the squared separation `2 - ε` gives
`‖·‖₂ ≥ 1/4`. -/
theorem isPestovHyperlinear_of_isHyperlinearGroup (h : IsHyperlinearGroup G) :
    IsPestovHyperlinear G := by
  intro F ε hε
  have hε2 : 0 < ε ^ 2 / 2 := div_pos (pow_pos hε 2) two_pos
  obtain ⟨Y, σ, hY, hU, hmul, hsep⟩ := h F (min (ε ^ 2 / 2) 1) (lt_min hε2 one_pos)
  refine ⟨{ carrier := Y, nonempty := hY, map := σ, isUnitary := hU,
            multiplicative := ?_, separated := ?_ }⟩
  · intro g hg h' hh' _
    rw [Real.sqrt_lt' hε]
    have h1 := hmul g hg h' hh'
    have h2 : min (ε ^ 2 / 2) 1 ≤ ε ^ 2 / 2 := min_le_left _ _
    linarith
  · intro g hg h' hh' hne
    rw [Real.le_sqrt' (by norm_num)]
    have hs := hsep g hg h' hh' hne
    have hm : min (ε ^ 2 / 2) 1 ≤ 1 := min_le_right _ _
    have hq : (1 / 4 : ℝ) ^ 2 = 1 / 16 := by norm_num
    rw [hq]
    linarith

end Pestov91

#print axioms Pestov91.test_hasPropertyT_of_finite
#print axioms Pestov91.test_hasPropertyT_intElementary
#print axioms Pestov91.test_infinite_intElementary
#print axioms Pestov91.test_infinite_propertyT_intElementaryModCentre
#print axioms Pestov91.test_not_hasPropertyT_int
#print axioms Pestov91.test_not_isKazhdanPair_int
#print axioms Pestov91.test_not_isKazhdanPair_of_nonpos
#print axioms Pestov91.test_isSoficGroup_of_finite
#print axioms Pestov91.test_isSoficGroup_int
#print axioms Pestov91.test_isHyperlinearGroup_of_finite
#print axioms Pestov91.test_isHyperlinearGroup_int
#print axioms Pestov91.test_soficSeparation_is_not_vacuous
#print axioms Pestov91.test_hyperlinearSeparation_is_not_vacuous
#print axioms Pestov91.test_isSoficGroup_model_injOn
#print axioms Pestov91.test_isHyperlinearGroup_model_injOn
#print axioms Pestov91.test_identity_clause_is_implied
#print axioms Pestov91.test_isSimpleGroup_zmod_two
#print axioms Pestov91.test_not_isSimpleGroup_punit
#print axioms Pestov91.test_finite_simple_group_meets_all_but_infinite
#print axioms Pestov91.test_int_meets_infinite_sofic_hyperlinear_not_propertyT
#print axioms Pestov91.isSoficGroup_iff_isPestovSofic
#print axioms Pestov91.isPestovHyperlinear_of_isHyperlinearGroup
