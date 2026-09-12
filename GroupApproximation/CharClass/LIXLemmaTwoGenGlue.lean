import GroupApproximation.CharClass.LIXLemmaTwoGenStepA
import GroupApproximation.CharClass.LIXStepDGenHalf
import GroupApproximation.CharClass.LIXKGenSection

/-!
# Lemma 2 at rank `n` from its two halves: the glue, and the coordinate swap

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.6; lead's rulings of 2026-09-11).

The endpoint's named proposition `ClimbedPowersOutside n` is reached through
`LemmaTwoHoldsForSections n (b k)`, i.e. `LIX.Gen.LemmaTwoFor n (lixDD n j) (b k j)` at every
stage `j`, with the degree-`k` family `b k j := KGen.bVecK n (k − 1)`.  Lemma 2 for one section
is the conjunction of three facts about one class `topClass` of mapping tori:

* **Step A** (`CharClass/LIXLemmaTwoGenStepA.lean`): an equivalence of the complements gives a
  corner unitary `G` with `G (e_last, 0) = (b, 0)`;
* **Step C** (`Gen.StepCHalf`, owned downstream by `lix-oddside-n`): the class does not vanish
  on the mapping torus of a corner unitary carrying `KGen`'s constant section `(e₀, 0)` to
  `(b, 0)`;
* **Step D** (`Gen.StepDHalf`, `CharClass/LIXStepDGenHalf.lean`): the class vanishes on the
  mapping torus of **every** corner unitary.

## The two conventions, and the swap

`LIX.Gen.LemmaTwoFor` sits inside the endpoint's named `Prop` and keeps the constant section
at `Gen.eLast n`, the pole of the analysis layer's generator.  `KGen` puts it at `e₀`, where
the `k` zeros of the degree-`k` section sit.  Both stay.  The bridge is made once, here: with
`τ` the coordinate swap `0 ↔ last` on the trivial block (identity on `H`), the corner unitary
`G' := G ∘ τ` (`(G m).submatrix id τ`) is again a continuous corner unitary of `V` — `τ` fixes
`V = 𝟏^{n+1} ⊕ H` — and it carries `(e₀, 0)` to `G (e_last, 0) = (b, 0)`.  So Step A at `e_last`
feeds Step C at `e₀` with the **same** section `b`, and Step D, being section-free, needs no
bridge at all.

## Main results

* `Gen.lastZeroSwap` — the swap `τ`; `Gen.isCornerUnitary_submatrix_lastZeroSwap` and
  `Gen.submatrix_lastZeroSwap_mulVec_eZero` — what `G ∘ τ` is.
* `Gen.StepCHalf` — the Step C half of Lemma 2 at rank `n`, at `KGen`'s `e₀` convention.
* `Gen.lemmaTwoFor_of_halves` — **Lemma 2 at rank `n` from the two halves**.
* `Gen.lemmaTwoFor_powers_of_halves` — the same for the degree-`k` family at every stage, in
  the quantifier shape of `Corollary4Powers n (fun k j => KGen.bVecK n (k − 1))`.
* `Gen.lemmaTwoFor_powers_of_stepC_modP` — the same with Step D discharged mod `p` by
  `Gen.stepDHalf_powers_of_modP`: only the Step C half and the mod-`p` data remain.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

namespace Gen

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The coordinate swap `0 ↔ last` -/

/-- The coordinate swap `0 ↔ last` on the trivial block `Fin (n + 1)`, the identity on `H`. -/
def lastZeroSwap (n : ℕ) (dd : Fin ℓ → ℕ) : VIdx n dd ≃ VIdx n dd :=
  Equiv.sumCongr (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) (Equiv.refl (HIdx dd))

/-- The swap carries the constant section `e₀` of `KGen` to the constant section `e_last` of
the shape layer. -/
theorem sumElim_eZero_comp_lastZeroSwap_symm (n : ℕ) :
    Sum.elim (KGen.eZero n) (0 : HIdx dd → ℂ) ∘ (lastZeroSwap n dd).symm
      = Sum.elim (eLast n) (0 : HIdx dd → ℂ) := by
  funext p
  cases p with
  | inl i =>
    show KGen.eZero n (Equiv.swap (0 : Fin (n + 1)) (Fin.last n) i) = eLast n i
    by_cases hl : i = Fin.last n
    · subst hl
      rw [Equiv.swap_apply_right, KGen.eZero_apply_zero, eLast, Pi.single_eq_same]
    · by_cases h0 : i = 0
      · subst h0
        have hne : Fin.last n ≠ 0 := fun h => hl h.symm
        rw [Equiv.swap_apply_left, KGen.eZero_apply_of_ne n hne, eLast, Pi.single_eq_of_ne hl]
      · rw [Equiv.swap_apply_of_ne_of_ne h0 hl, KGen.eZero_apply_of_ne n h0, eLast,
          Pi.single_eq_of_ne hl]
  | inr j => rfl

/-- The swap fixes `V = 𝟏^{n+1} ⊕ H`. -/
theorem Vmat_submatrix_lastZeroSwap (n : ℕ) (m : baseM n dd) :
    (Vmat n m).submatrix (lastZeroSwap n dd) (lastZeroSwap n dd) = Vmat n m := by
  ext p q
  cases p with
  | inl i => cases q with
    | inl j =>
      show (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Equiv.swap 0 (Fin.last n) i)
          (Equiv.swap 0 (Fin.last n) j) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j
      simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
    | inr j => rfl
  | inr i => cases q with
    | inl j => rfl
    | inr j => rfl

/-- **`G ∘ τ` is a corner unitary of `V` whenever `G` is.** -/
theorem isCornerUnitary_submatrix_lastZeroSwap (n : ℕ) {m : baseM n dd}
    {G : Matrix (VIdx n dd) (VIdx n dd) ℂ} (hG : IsCornerUnitary (Vmat n m) G) :
    IsCornerUnitary (Vmat n m) (G.submatrix id (lastZeroSwap n dd)) where
  proj := hG.proj
  star_mul_self := by
    rw [Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul Gᴴ G (lastZeroSwap n dd) id (lastZeroSwap n dd)
        Function.bijective_id,
      hG.star_mul_self, Matrix.submatrix_one_equiv]
  mul_star_self := by
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv G Gᴴ id (lastZeroSwap n dd) id, hG.mul_star_self,
      Matrix.submatrix_id_id]
  commutes := by
    calc G.submatrix id (lastZeroSwap n dd) * Vmat n m
        = G.submatrix id (lastZeroSwap n dd)
            * (Vmat n m).submatrix (lastZeroSwap n dd) (lastZeroSwap n dd) := by
          rw [Vmat_submatrix_lastZeroSwap]
      _ = (G * Vmat n m).submatrix id (lastZeroSwap n dd) :=
          Matrix.submatrix_mul_equiv G (Vmat n m) id (lastZeroSwap n dd) (lastZeroSwap n dd)
      _ = (Vmat n m * G).submatrix id (lastZeroSwap n dd) := by rw [hG.commutes]
      _ = (Vmat n m).submatrix id id * G.submatrix id (lastZeroSwap n dd) :=
          Matrix.submatrix_mul (Vmat n m) G id id (lastZeroSwap n dd) Function.bijective_id
      _ = Vmat n m * G.submatrix id (lastZeroSwap n dd) := by rw [Matrix.submatrix_id_id]

/-- **`G ∘ τ` carries `(e₀, 0)` where `G` carries `(e_last, 0)`.** -/
theorem submatrix_lastZeroSwap_mulVec_eZero (n : ℕ) (G : Matrix (VIdx n dd) (VIdx n dd) ℂ) :
    G.submatrix id (lastZeroSwap n dd) *ᵥ Sum.elim (KGen.eZero n) (0 : HIdx dd → ℂ)
      = G *ᵥ Sum.elim (eLast n) (0 : HIdx dd → ℂ) := by
  rw [Matrix.submatrix_mulVec_equiv, sumElim_eZero_comp_lastZeroSwap_symm, Function.comp_id]

/-! ## 2. The Step C half at `KGen`'s convention -/

/-- **The Step C half of Lemma 2 at rank `n`**, for the section `b` and the class `topClass`,
at `KGen`'s convention: the class does not vanish on the mapping torus of any continuous
corner unitary of `V` carrying the constant section `(e₀, 0)` (`KGen.aVecK`) to `(b, 0)`.

The seam hypothesis is spelled exactly as `KGen.lixKSection_eq_zero_iff`'s `hGe`, so a Step C
theorem over `KGen.lixKSection n k G` discharges this at `b = KGen.bVecK n k` with no bridge. -/
def StepCHalf (n : ℕ) (dd : Fin ℓ → ℕ) (b : baseM n dd → Fin (n + 1) → ℂ) {K : Type*} [Zero K]
    (topClass : (↥sphereOne × baseM n dd →
      Matrix (VIdx n dd ⊕ VIdx n dd) (VIdx n dd ⊕ VIdx n dd) ℂ) → K) : Prop :=
  ∀ G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ, Continuous G →
    (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
    (∀ m, G m *ᵥ Sum.elim (KGen.aVecK n m) 0 = Sum.elim (b m) 0) →
    topClass (mappingTorus (Vmat n) G circHoriz circHeight) ≠ 0

/-! ## 3. The glue -/

/-- **Lemma 2 at rank `n`, from its two halves.**  For a continuous unit section `b` of the
trivial block, the Step C half at `e₀` and the Step D half give
`LIX.Gen.LemmaTwoFor n dd b`: the complement of `b` and the complement of `e_last` are not
Murray--von Neumann equivalent as continuous fields.

Step A produces `G` with `G (e_last, 0) = (b, 0)`; `G ∘ τ` is a corner unitary carrying
`(e₀, 0)` to `(b, 0)`; Step C says its class is nonzero, Step D that it is zero. -/
theorem lemmaTwoFor_of_halves (n : ℕ) {b : baseM n dd → Fin (n + 1) → ℂ}
    (hbc : Continuous b) (hb : ∀ m, ∑ i, ‖b m i‖ ^ 2 = 1) {K : Type*} [Zero K]
    {topClass : (↥sphereOne × baseM n dd →
      Matrix (VIdx n dd ⊕ VIdx n dd) (VIdx n dd ⊕ VIdx n dd) ℂ) → K}
    (hC : StepCHalf n dd b topClass) (hD : StepDHalf n dd topClass) :
    LIX.Gen.LemmaTwoFor n dd b := by
  intro h
  obtain ⟨G, hGc, hGu, hGe⟩ := exists_cornerUnitary_of_continuousMvNEquiv n hbc hb h
  have hGc' : Continuous fun m => (G m).submatrix id (lastZeroSwap n dd) :=
    hGc.matrix_submatrix id (lastZeroSwap n dd)
  have hGu' : ∀ m, IsCornerUnitary (Vmat n m) ((G m).submatrix id (lastZeroSwap n dd)) :=
    fun m => isCornerUnitary_submatrix_lastZeroSwap n (hGu m)
  have hGe' : ∀ m, (G m).submatrix id (lastZeroSwap n dd) *ᵥ Sum.elim (KGen.aVecK n m) 0
      = Sum.elim (b m) 0 :=
    fun m => (submatrix_lastZeroSwap_mulVec_eZero n (G m)).trans (hGe m)
  exact hC _ hGc' hGu' hGe' (hD _ hGc' hGu')

/-- **Lemma 2 for the degree-`k` family at every stage, from the two halves.**  For a prime
(or any natural) `p`, every exponent `k` with `p ∤ k` and every stage `j`, the section
`KGen.bVecK n (k − 1)` satisfies `LIX.Gen.LemmaTwoFor n (lixDD n j) _`.  The conclusion is
`LemmaTwoHoldsForSections n (fun j => KGen.bVecK n (k − 1))` unfolded, which is the
hypothesis `Corollary4Powers n (fun k j => KGen.bVecK n (k − 1))` consumes. -/
theorem lemmaTwoFor_powers_of_halves (n p : ℕ) {K : ℕ → Type*} [∀ j, Zero (K j)]
    (topClass : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) → K j)
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      StepCHalf n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) (topClass j))
    (hD : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ, StepDHalf n (LIX.Gen.lixDD n j) (topClass j)) :
    ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) :=
  fun k hk j => lemmaTwoFor_of_halves n (KGen.continuous_bVecK n (k - 1))
    (KGen.bVecK_normSq n (k - 1)) (hC k hk j) (hD k hk j)

/-- **Lemma 2 for the degree-`k` family, with Step D discharged mod `p`.**  At a prime
`p ∣ n`, given the mod-`p` data of every stage and the Step C half at the top mod-`p` Chern
class, every exponent `k` with `p ∤ k` gives Lemma 2 at every stage.  What remains owed is
exactly the Step C half and the producers of `Gen.ModPStepDData`'s fields. -/
theorem lemmaTwoFor_powers_of_stepC_modP (n p : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hpn : p ∣ n)
    {R H : ℕ → Type*} [∀ j, CommRing (R j)] [∀ j, CommRing (H j)] [∀ j, ExpChar (R j) p]
    (γfun : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) → ℕ → H j)
    (data : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      ModPStepDData n p (LIX.Gen.lixDD n j) (R j) (H j)
        (γfun j (mappingTorus (Vmat n) G circHoriz circHeight)))
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      StepCHalf n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1))
        (fun W => γfun j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1)))) :
    ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) :=
  lemmaTwoFor_powers_of_halves n p
    (fun j W => γfun j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1))) hC
    (stepDHalf_powers_of_modP n p hp hn hpn γfun data)

end Gen

#audit_axioms Gen.sumElim_eZero_comp_lastZeroSwap_symm
#audit_axioms Gen.Vmat_submatrix_lastZeroSwap
#audit_axioms Gen.isCornerUnitary_submatrix_lastZeroSwap
#audit_axioms Gen.submatrix_lastZeroSwap_mulVec_eZero
#audit_axioms Gen.StepCHalf
#audit_axioms Gen.lemmaTwoFor_of_halves
#audit_axioms Gen.lemmaTwoFor_powers_of_halves
#audit_axioms Gen.lemmaTwoFor_powers_of_stepC_modP

end GroupApproximation.CharClass

end
