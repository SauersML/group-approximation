import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelPsi
import GroupApproximation.Meta.AxiomGuard

/-!
# `Ψ ∘ snd = inl ∘ q` on the relative subgroup, and dying

Lane `bh-met-91g`, injectivity module.  With `q`, `α` as in `ElemFPK2PullRelPsi`, and `α`
also satisfying `k2PullRel_Compat`:

* `k2PullRel_psi_snd`: for `y` in the closure of the relative generators,
  `Ψ(snd y) = inl (q y)`.  The proof inducts over the closure.  On a generator
  `const(d) · x_ij(b) · const(d)⁻¹` with `fst b = 0`, `Ψ` sends `snd` of it to
  `inr(λ d) · (u_ij(snd b), 1) · inr(λ d)⁻¹`.  Here `u_ij(snd b) = q(x_ij(b))`, because
  `lift (snd b) = b`, and `x_ij((snd b)(0)) = x_ij(λ(fst b)) = 1`.  `Compat` then identifies
  the conjugate with `inl (q (const(d) x_ij(b) const(d)⁻¹))`.
* `k2PullRel_Faithful q`: every `y ∈ ker fst` with `q y = 1` dies after padding.
* `k2PullRel_stDies_of_ringMap`: if `fst y = 1` and `snd y = 1`, and `q` is faithful, then `y`
  dies after padding.  By relative generation (`k2PullRel_mem_closure_of_ringMap_eq_one`), `y`
  is in the closure, so `inl (q y) = Ψ(snd y) = Ψ(1) = 1` and `q y = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section PullRelInj

variable {A : Type*} [CommRing A] {s : A} {M : ℕ} {H : Type*} [Group H]
  (q : k2PullRel_ker s M →* H) (α : SteinbergGroup (Fin M) (Localization.Away s) →* MulAut H)

/-- `Ψ(x_ij(snd b)) = inl (q (x_ij(b)))` when `fst b = 0`. -/
theorem k2PullRel_elt_snd (i j : Fin M) (hij : i ≠ j) {b : k2DilateSt_pullback s}
    (hb : k2PullRel_fst s b = 0) :
    k2PullRel_elt q α i j hij (k2PullRel_snd s b) =
      SemidirectProduct.inl (q ⟨x i j hij b, k2PullRel_x_mem i j hij hb⟩) := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [k2PullRel_elt_left, SemidirectProduct.left_inl]
    unfold k2PullRel_u
    exact congrArg q (Subtype.ext (congrArg (x i j hij) (k2PullRel_lift_snd hb)))
  · rw [k2PullRel_elt_right, SemidirectProduct.right_inl, k2PullRel_eval_snd, hb, map_zero,
      x_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_elt_snd

/-- **`Ψ ∘ snd = inl ∘ q`** on the closure of the relative generators. -/
theorem k2PullRel_psi_snd (hF1 : k2PullRel_F1 q α) (hF2 : k2PullRel_F2 q α)
    (hF3 : k2PullRel_F3 q α) (hC : k2PullRel_Compat q α)
    {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (hy : y ∈ Subgroup.closure
      (k2PullRel_genSet (I := Fin M) (k2PullRel_const s) (k2PullRel_fst s))) :
    ∀ hk : y ∈ k2PullRel_ker s M, k2PullRel_psi q α hF1 hF2 hF3 (ringMap (k2PullRel_snd s) y) =
      SemidirectProduct.inl (q ⟨y, hk⟩) := by
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    intro hk
    obtain ⟨d, i, j, hij, b, hb, rfl⟩ := hg
    have hL : k2PullRel_psi q α hF1 hF2 hF3 (ringMap (k2PullRel_snd s)
        (ringMap (k2PullRel_const s) d * x i j hij b * (ringMap (k2PullRel_const s) d)⁻¹)) =
        SemidirectProduct.inr (ringMap (algebraMap A (Localization.Away s)) d) *
          k2PullRel_elt q α i j hij (k2PullRel_snd s b) *
          SemidirectProduct.inr (ringMap (algebraMap A (Localization.Away s)) d)⁻¹ := by
      simp only [map_mul, map_inv, k2PullRel_ringMap_snd_const, k2PullRel_psi_C, ringMap_x,
        k2PullRel_psi_x]
    rw [hL, k2PullRel_elt_snd q α i j hij hb, ← SemidirectProduct.inl_aut, hC d i j hij b hb]
  | one =>
    intro hk
    have h1 : (⟨1, hk⟩ : k2PullRel_ker s M) = 1 := rfl
    rw [h1]
    simp only [map_one]
  | mul g h hg hh ihg ihh =>
    intro hk
    have hgk := k2PullRel_closure_le_ker hg
    have hhk := k2PullRel_closure_le_ker hh
    have e : (⟨g * h, hk⟩ : k2PullRel_ker s M) = ⟨g, hgk⟩ * ⟨h, hhk⟩ := rfl
    rw [e]
    simp only [map_mul]
    rw [ihg hgk, ihh hhk]
  | inv g hg ih =>
    intro hk
    have hgk := k2PullRel_closure_le_ker hg
    have e : (⟨g⁻¹, hk⟩ : k2PullRel_ker s M) = (⟨g, hgk⟩ : k2PullRel_ker s M)⁻¹ := rfl
    rw [e]
    simp only [map_inv]
    rw [ih hgk]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_psi_snd

/-- **Faithfulness**: `q y = 1` forces `y` to die after padding. -/
def k2PullRel_Faithful : Prop :=
  ∀ y : k2PullRel_ker s M, q y = 1 →
    cubeDiagDilate_StDies (y : SteinbergGroup (Fin M) (k2DilateSt_pullback s))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_Faithful

/-- **Dying**: `fst y = 1` and `snd y = 1` make `y` die after padding, given the action data. -/
theorem k2PullRel_stDies_of_ringMap (hF1 : k2PullRel_F1 q α) (hF2 : k2PullRel_F2 q α)
    (hF3 : k2PullRel_F3 q α) (hC : k2PullRel_Compat q α) (hQ : k2PullRel_Faithful q)
    {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (h₁ : ringMap (k2PullRel_fst s) y = 1) (h₂ : ringMap (k2PullRel_snd s) y = 1) :
    cubeDiagDilate_StDies y := by
  have hy := k2PullRel_mem_closure_of_ringMap_eq_one (k2PullRel_const s) (k2PullRel_fst s)
    (k2PullRel_fst_const s) h₁
  have hk := k2PullRel_closure_le_ker hy
  have e := k2PullRel_psi_snd q α hF1 hF2 hF3 hC hy hk
  rw [h₂, map_one] at e
  have hq : q ⟨y, hk⟩ = 1 := by
    apply SemidirectProduct.inl_injective (φ := α)
    rw [map_one]
    exact e.symm
  exact hQ ⟨y, hk⟩ hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_stDies_of_ringMap

end PullRelInj

end GroupApproximation.BooneHigman.Metabelian.ElemFP
