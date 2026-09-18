import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCornerShift.Conjugation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Stabilization

/-!
# Diagonal corner maps of Steinberg groups (lane LVCornerShift)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; ABC 2009, proof of
`thm:skewyao`, Step 3.  For functions `σ τ : I → S` with `τ i * σ i = 1` the assignment
`x_{ij}(a) ↦ x_{ij}(σ i * a * τ j)` respects the Steinberg relations, so it defines an
endomorphism `cornerMap σ τ` of `St_I(S)`.  It is the Steinberg-level version of conjugating a
matrix by the diagonal matrices `diag σ` and `diag τ`.

* `cornerMap_eq_self`: for `σ = τ = 1` it is the identity;
* `cornerConj_castSuccStab_cornerMap`: after one stabilization, conjugation by the corner element
  `cornerConj` on the indices `m`, `last n` turns `cornerMap σ τ` into `cornerMap σ' τ'`, where
  `σ'`, `τ'` differ from `σ`, `τ` only at `m`, with `σ' m = u * σ m` and `τ' m = τ m * v`.
-/

namespace GroupApproximation.Full.LVCornerShift

open SteinbergGroup
open scoped commutatorElement

section CornerMap

variable {I : Type*} [Fintype I] [DecidableEq I] {S : Type*} [Ring S]

/-- The generator assignment `x_{ij}(a) ↦ x_{ij}(σ i * a * τ j)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def cornerGenerator (σ τ : I → S) (g : SteinbergGenerator I S) : SteinbergGroup I S :=
  x g.row g.column g.row_ne_column (σ g.row * g.coefficient * τ g.column)

/-- The corner assignment kills the Steinberg relators when `τ i * σ i = 1`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerGenerator_relation (σ τ : I → S) (hστ : ∀ i, τ i * σ i = 1)
    (w : FreeGroup (SteinbergGenerator I S)) (hw : w ∈ relations (I := I) (R := S)) :
    FreeGroup.lift (cornerGenerator σ τ) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, cornerGenerator]
      change x i j hij (σ i * a * τ j) * x i j hij (σ i * b * τ j) *
        (x i j hij (σ i * (a + b) * τ j))⁻¹ = 1
      rw [x_mul, mul_add, add_mul, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, cornerGenerator]
      change ⁅x i j hij (σ i * a * τ j), x k l hkl (σ k * b * τ l)⁆ = 1
      exact (x_commute_of_ne i j k l hij hkl hjk hli (σ i * a * τ j)
        (σ k * b * τ l)).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        cornerGenerator]
      change ⁅x i j hij (σ i * a * τ j), x j k hjk (σ j * b * τ k)⁆ *
        (x i k hik (σ i * (a * b) * τ k))⁻¹ = 1
      have hc : σ i * a * τ j * (σ j * b * τ k) = σ i * (a * b) * τ k := by
        rw [show σ i * a * τ j * (σ j * b * τ k) = σ i * a * (τ j * σ j) * b * τ k by
          simp only [mul_assoc], hστ j, mul_one, mul_assoc (σ i) a b]
      rw [x_commutator i j k hij hjk hik, hc, mul_inv_cancel]

/-- The corner endomorphism `x_{ij}(a) ↦ x_{ij}(σ i * a * τ j)` of `St_I(S)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def cornerMap (σ τ : I → S) (hστ : ∀ i, τ i * σ i = 1) :
    SteinbergGroup I S →* SteinbergGroup I S :=
  PresentedGroup.toGroup (f := cornerGenerator σ τ) (cornerGenerator_relation σ τ hστ)

/-- `cornerMap σ τ` on generators.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem cornerMap_x (σ τ : I → S) (hστ : ∀ i, τ i * σ i = 1) (i j : I) (hij : i ≠ j) (a : S) :
    cornerMap σ τ hστ (x i j hij a) = x i j hij (σ i * a * τ j) := by
  exact PresentedGroup.toGroup.of _

/-- The corner map with trivial diagonals is the identity.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerMap_eq_self (σ τ : I → S) (hστ : ∀ i, τ i * σ i = 1) (hσ : ∀ i, σ i = 1)
    (hτ : ∀ i, τ i = 1) (g : SteinbergGroup I S) : cornerMap σ τ hστ g = g := by
  have hh : cornerMap σ τ hστ = MonoidHom.id (SteinbergGroup I S) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change cornerMap σ τ hστ (x i j hij a) = x i j hij a
    rw [cornerMap_x, hσ, hτ, one_mul, mul_one]
  exact DFunLike.congr_fun hh g

/-- Generators with equal indices are equal.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem x_eq_of_eq {i j i' j' : I} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i') (hj : j = j')
    (a : S) : x i j hij a = x i' j' hij' a := by
  subst hi
  subst hj
  rfl

end CornerMap

section Step

variable {S : Type*} [Ring S]

/-- **Corner shift step** (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; ABC 2009,
proof of `thm:skewyao`, Step 3).  After stabilizing `St_n(S) → St_{n+1}(S)`, conjugation by the
corner element on the indices `m`, `last n` multiplies the diagonal data of a corner map at `m`
by `u` on the left and by `v` on the right. -/
theorem cornerConj_castSuccStab_cornerMap {n : ℕ} {u v : S} (hvu : v * u = 1) (m : Fin n)
    (σ τ σ' τ' : Fin n → S) (hστ : ∀ i, τ i * σ i = 1) (hστ' : ∀ i, τ' i * σ' i = 1)
    (hσm : σ' m = u * σ m) (hτm : τ' m = τ m * v)
    (hσo : ∀ j, j ≠ m → σ' j = σ j) (hτo : ∀ j, j ≠ m → τ' j = τ j)
    (g : SteinbergGroup (Fin n) S) :
    cornerConj (Fin.castSucc_ne_last m) u v *
        LVCentral.castSuccStab n S (cornerMap σ τ hστ g) *
        (cornerConj (Fin.castSucc_ne_last m) u v)⁻¹ =
      LVCentral.castSuccStab n S (cornerMap σ' τ' hστ' g) := by
  have hh : (MulAut.conj (cornerConj (Fin.castSucc_ne_last m) u v)).toMonoidHom.comp
      ((LVCentral.castSuccStab n S).comp (cornerMap σ τ hστ)) =
      (LVCentral.castSuccStab n S).comp (cornerMap σ' τ' hστ') := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change cornerConj (Fin.castSucc_ne_last m) u v *
        LVCentral.castSuccStab n S (cornerMap σ τ hστ (x i j hij a)) *
        (cornerConj (Fin.castSucc_ne_last m) u v)⁻¹ =
      LVCentral.castSuccStab n S (cornerMap σ' τ' hστ' (x i j hij a))
    rw [cornerMap_x, cornerMap_x, LVCentral.castSuccStab_x, LVCentral.castSuccStab_x]
    by_cases hi : i = m
    · have hjm : j ≠ m := fun e => hij (hi.trans e.symm)
      subst hi
      rw [hσm, hτo j hjm, cornerConj_x_left _ _ (Fin.castSucc_ne_last j).symm hvu]
      simp only [mul_assoc]
    · by_cases hj : j = m
      · have him : i ≠ m := fun e => hij (e.trans hj.symm)
        subst hj
        rw [hσo i him, hτm, cornerConj_x_right _ _ (Fin.castSucc_ne_last i) hvu]
        simp only [mul_assoc]
      · have hiA : i.castSucc ≠ m.castSucc := fun e => hi (Fin.castSucc_inj.mp e)
        have hjA : j.castSucc ≠ m.castSucc := fun e => hj (Fin.castSucc_inj.mp e)
        rw [hσo i hi, hτo j hj, cornerConj_x_other (Fin.castSucc_ne_last m) _ hiA
          (Fin.castSucc_ne_last i) hjA (Fin.castSucc_ne_last j)]
  exact DFunLike.congr_fun hh g

end Step

end GroupApproximation.Full.LVCornerShift
