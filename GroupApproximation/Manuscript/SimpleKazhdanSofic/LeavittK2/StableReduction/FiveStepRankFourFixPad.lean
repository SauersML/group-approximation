import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepRankFourFixConj
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCornerInjTransport
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import GroupApproximation.Algebra.ElementaryPaddingInjective
import GroupApproximation.Meta.AxiomGuard

/-!
# The corner endomorphism fixes stabilized `K₂` (sk-leavitt-36b, 2)

Let `R` be a ring with a Leavitt family `L`, `σ_r = fiveStepCornerHom L r` and
`pad = stab n R : St_n(R) → St_{n+1}(R)`.  From the conjugation identity
`C · pad(w) · C⁻¹ = pad(σ_r w)` (`fiveStepRankFourFix_conj_stab`), together with the padded
centrality `pad(K₂(n)) ≤ Z(St_{n+1})` (`map_stab_K2_le_center`), this file proves the following,
all unconditionally:

* `pad(σ_r k) = pad(k)` for `k ∈ K₂(n)` (`fiveStepRankFourFix_stab_cornerHom_of_mem_K2`);
* `σ_{castSucc r}` fixes `pad(K₂(n))` pointwise (`fiveStepRankFourFix_cornerHom_stab_of_mem_K2`);
* **surjective stability gives the fixed point**: if `K₂(n+1) ≤ pad(K₂(n))`, then
  `σ_{castSucc r}` fixes `K₂(n+1)` pointwise (`fiveStepRankFourFix_fix_of_le_map_stab`);
* **injective stability gives the fixed point**: if `K₂(n) → K₂(n+1)` is injective
  (`Full.LVH2GL3.K2StabInjective R n`), then `σ_r` fixes `K₂(n)` pointwise
  (`fiveStepRankFourFix_cornerHom_eq_of_k2StabInjective`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ}

/-- **`σ_r` acts trivially on `K₂(n)` after one stabilization.**  `pad(k)` is central, so the
conjugation by `C` realizing `pad ∘ σ_r` fixes it. -/
theorem fiveStepRankFourFix_stab_cornerHom_of_mem_K2 (r : Fin n)
    {k : SteinbergGroup (Fin n) R} (hk : k ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R) :
    BooneHigman.SteinbergBasic.stab n R (fiveStepCornerHom L r k) =
      BooneHigman.SteinbergBasic.stab n R k := by
  have hc : BooneHigman.SteinbergBasic.stab n R k ∈
      Subgroup.center (BooneHigman.SteinbergBasic.St (n + 1) R) :=
    map_stab_K2_le_center (Subgroup.mem_map_of_mem (BooneHigman.SteinbergBasic.stab n R) hk)
  rw [← fiveStepRankFourFix_conj_stab L r k, Subgroup.mem_center_iff.mp hc, mul_inv_cancel_right]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_stab_cornerHom_of_mem_K2

/-- **`σ_{castSucc r}` fixes `pad(K₂(n))` pointwise**: transport `σ` along `pad`
(`fiveStepCornerInj_cornerHom_indexMap`), then use the previous lemma. -/
theorem fiveStepRankFourFix_cornerHom_stab_of_mem_K2 (r : Fin n)
    {k : SteinbergGroup (Fin n) R} (hk : k ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R) :
    fiveStepCornerHom L (Fin.castSucc r) (BooneHigman.SteinbergBasic.stab n R k) =
      BooneHigman.SteinbergBasic.stab n R k := by
  have h1 := fiveStepCornerInj_cornerHom_indexMap L Fin.castSuccEmb r (Fin.castSucc r) rfl k
  have h2 := fiveStepRankFourFix_stab_cornerHom_of_mem_K2 L r hk
  exact h1.trans h2

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_cornerHom_stab_of_mem_K2

/-- **Surjective stability gives the fixed point.**  If every element of `K₂(n+1)` is padded
from `K₂(n)`, then `σ_{castSucc r}` fixes `K₂(n+1)` pointwise. -/
theorem fiveStepRankFourFix_fix_of_le_map_stab (r : Fin n)
    (h : BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R ≤
      (BooneHigman.SteinbergBasic.K2 (Fin n) R).map (BooneHigman.SteinbergBasic.stab n R)) :
    ∀ w ∈ BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R,
      fiveStepCornerHom L (Fin.castSucc r) w = w := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp (h hw)
  exact fiveStepRankFourFix_cornerHom_stab_of_mem_K2 L r hk

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_fix_of_le_map_stab

/-- **Injective stability gives the fixed point.**  If `K₂(n) → K₂(n+1)` is injective, then
`σ_r` fixes `K₂(n)` pointwise: `σ_r k · k⁻¹` lies in `K₂(n)` and dies after padding. -/
theorem fiveStepRankFourFix_cornerHom_eq_of_k2StabInjective (r : Fin n)
    (h : Full.LVH2GL3.K2StabInjective R n) {k : SteinbergGroup (Fin n) R}
    (hk : k ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R) :
    fiveStepCornerHom L r k = k := by
  have hemb : (Fin.castLEEmb (Nat.le_succ n) : Fin n ↪ Fin (n + 1)) = Fin.castSuccEmb :=
    Function.Embedding.ext fun _ => Fin.ext rfl
  have hs := fiveStepRankFourFix_stab_cornerHom_of_mem_K2 L r hk
  have h1 : indexMap (R := R) (Fin.castLEEmb (Nat.le_succ n))
      (fiveStepCornerHom L r k * k⁻¹) = 1 := by
    rw [hemb, map_mul, map_inv]
    exact mul_inv_eq_one.mpr hs
  have hp : projection (fiveStepCornerHom L r k * k⁻¹) = 1 := by
    have h2 := Full.LVH2GL3.projection_indexMap (Fin.castLEEmb (Nat.le_succ n))
      (fiveStepCornerHom L r k * k⁻¹)
    rw [h1, map_one] at h2
    exact ElementaryPadding.elementaryPad_injective (R := R) (Fin.castLEEmb (Nat.le_succ n))
      (by rw [map_one]; exact h2.symm)
  exact mul_inv_eq_one.mp (h _ hp h1)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_cornerHom_eq_of_k2StabInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
