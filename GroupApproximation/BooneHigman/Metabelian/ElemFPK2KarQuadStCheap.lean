import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarQuadRelStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Four relative conjugates: the stably datum-cheap case (Hurwitz orbit of rank-one pairs)

Lane `bh-met-93w`, core module.  `P = k2DilateSt_pullback s`, `A` a domain, `s ≠ 0`.

* `k2KarQuadSt_DatumCheap y`: some padding of `y`, conjugated by some `c`, equals
  `Y · (g₃ x_kl(c₃) g₃⁻¹) · (g₄ x_ij(c₄) g₄⁻¹)` with `(Y, V, W)` a rank-one datum
  (`stab Y = ⁅padCol V, padRow W⁆`, `padMat Y = 1 + V Wᵀ`, `W ⬝ᵥ V = 0`).
* **`k2KarQuadSt_stDies_of_datumCheap`**: a datum-cheap `y` with `St(snd) y = 1` dies after
  padding (`k2KarQuad_stDies_datum_mul_two`, conjugation and padding invariance of death).
* **`k2KarQuadSt_datumCheap_of_factor`**: if a padded conjugate of `y` is `w₁ w₂ w₃ w₄` with all
  `wᵢ` relative conjugates and `PairRankOne (w₁ w₂)`, then `y` is datum-cheap
  (`k2KarTri_rankOneAt_two` upgrades `w₁ w₂` to a rank-one datum).
* **Pair lemmas** `k2KarQuadSt_datumCheap_of_pair12/23/13/24`: `z₁ z₂ z₃ z₄` is datum-cheap as
  soon as ONE of `z₁ z₂`, `z₂ z₃`, `z₁ z₃`, `z₂ z₄` is `PairRankOne`.  The pairs `(1,3)` and
  `(2,4)` are NEW (only `(1,2)`, `(2,3)` were handled in `bh-met-93q`); they come from the
  Steinberg-level Hurwitz moves
  `z₁ z₂ z₃ z₄ = b · z₁ z₃ z₄`, `b = z₁ z₂ z₁⁻¹`, and
  `z₁ z₂ z₃ z₄ = z₁ c' · z₂ z₄`, `c' = z₂ z₃ z₂⁻¹`, followed by rotation
  (free-group identities, checked in `bh-met-93w/truth_check.py`).

Truth check (`bh-met-93w/truth_check.py`, over `ℤ[T]`): there are relative tuples with product
`1`, both adjacent pairs of rank `2` (so outside `bh-met-93q`), but `z₁ z₃ = 1 + V Wᵀ`,
`W ⬝ᵥ V = 0`; so the new class meets the domain of `k2KarQuad_GenericAt`.

Relativity is used only for the shape `g x_ij(b) g⁻¹`; `snd` only via `padMat`
(`k2KarInd_padMat_eq_one`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarQuadStCheapDef

/-- **Stably datum-cheap**: a padded conjugate of `y` is a rank-one datum times two
conjugated root elements. -/
def k2KarQuadSt_DatumCheap {A : Type*} [CommRing A] {s : A} {M : ℕ}
    (y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)) : Prop :=
  ∃ (M' : ℕ) (hM : M ≤ M') (c Y g₃ g₄ : St M' (k2DilateSt_pullback s))
    (V W : Fin M' → k2DilateSt_pullback s) (k l : Fin M') (hkl : k ≠ l)
    (c₃ : k2DilateSt_pullback s) (i j : Fin M') (hij : i ≠ j) (c₄ : k2DilateSt_pullback s),
    stab M' (k2DilateSt_pullback s) Y = ⁅padCol V, padRow W⁆ ∧
      padMat Y = 1 + Matrix.vecMulVec V W ∧ W ⬝ᵥ V = 0 ∧
        c * SteinbergGroup.indexMap (Fin.castLEEmb hM) y * c⁻¹ =
          Y * (g₃ * x k l hkl c₃ * g₃⁻¹) * (g₄ * x i j hij c₄ * g₄⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_DatumCheap

/-- Padding along `le_refl` is the identity. -/
theorem k2KarQuadSt_indexMap_refl {R : Type*} [Ring R] {M : ℕ}
    (y : SteinbergGroup (Fin M) R) :
    SteinbergGroup.indexMap (Fin.castLEEmb (le_refl M)) y = y := by
  have hh : SteinbergGroup.indexMap (R := R) (Fin.castLEEmb (le_refl M)) = MonoidHom.id _ := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change SteinbergGroup.indexMap (Fin.castLEEmb (le_refl M)) (x i j hij a) = x i j hij a
    exact SteinbergGroup.indexMap_x (Fin.castLEEmb (le_refl M)) i j hij a
  exact DFunLike.congr_fun hh y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_indexMap_refl

end KarQuadStCheapDef

section KarQuadStCheap

variable {A : Type*} [CommRing A] [IsDomain A] {s : A}

/-- **The cheap case dies**: a datum-cheap `y` with `St(snd) y = 1` dies after padding. -/
theorem k2KarQuadSt_stDies_of_datumCheap (hs : s ≠ 0) {M : ℕ}
    {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (hsnd : ringMap (k2PullRel_snd s) y = 1) (h : k2KarQuadSt_DatumCheap y) :
    cubeDiagDilate_StDies y := by
  obtain ⟨M', hM, c, Y, g₃, g₄, V, W, k, l, hkl, c₃, i, j, hij, c₄, hst, hm, hd, he⟩ := h
  refine cubeDiagDilate_stDies_of_indexMap hM ?_
  have hsnd' : ringMap (k2PullRel_snd s)
      (c * SteinbergGroup.indexMap (Fin.castLEEmb hM) y * c⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, ← GroupApproximation.Full.LVStableK2.indexMap_ringMap, hsnd,
      map_one, mul_one, mul_inv_cancel]
  have hc : cubeDiagDilate_StDies (c * SteinbergGroup.indexMap (Fin.castLEEmb hM) y * c⁻¹) := by
    rw [he] at hsnd' ⊢
    exact k2KarQuad_stDies_datum_mul_two (k2KarInd_mul_eq_zero hs) hst hm hd g₃ k l hkl c₃
      g₄ i j hij c₄ (k2KarInd_padMat_eq_one hs hsnd')
  have e : c⁻¹ * (c * SteinbergGroup.indexMap (Fin.castLEEmb hM) y * c⁻¹) * c⁻¹⁻¹ =
      SteinbergGroup.indexMap (Fin.castLEEmb hM) y := by
    group
  have h' := cubeDiagDilate_stDies_conj c⁻¹ hc
  rwa [e] at h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_stDies_of_datumCheap

/-- **Factorization criterion**: a padded conjugate `w₁ w₂ w₃ w₄` of `y` (relative conjugates)
with `PairRankOne (w₁ w₂)` makes `y` datum-cheap. -/
theorem k2KarQuadSt_datumCheap_of_factor (hs : s ≠ 0) {M M' : ℕ} (hM : M ≤ M')
    {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (c : SteinbergGroup (Fin M') (k2DilateSt_pullback s))
    {w₁ w₂ w₃ w₄ : SteinbergGroup (Fin M') (k2DilateSt_pullback s)}
    (h₁ : w₁ ∈ k2KarRel_gens s M') (h₂ : w₂ ∈ k2KarRel_gens s M')
    (h₃ : w₃ ∈ k2KarRel_gens s M') (h₄ : w₄ ∈ k2KarRel_gens s M')
    (he : c * SteinbergGroup.indexMap (Fin.castLEEmb hM) y * c⁻¹ = w₁ * w₂ * w₃ * w₄)
    (hp : k2KarQuad_PairRankOne (w₁ * w₂)) : k2KarQuadSt_DatumCheap y := by
  obtain ⟨V, W, hm, hd⟩ := hp
  have e : [w₁, w₂].prod = w₁ * w₂ := by
    rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
  have hl : ∀ z ∈ [w₁, w₂], z ∈ k2KarRel_gens s M' := by
    intro z hz
    rcases List.mem_pair.mp hz with rfl | rfl
    · exact h₁
    · exact h₂
  obtain ⟨V', W', hs', hm'⟩ := k2KarTri_rankOneAt_two hs M' [w₁, w₂] (by simp) hl V W
    (by rw [e]; exact hm) hd
  rw [e] at hs' hm'
  have hd' : W' ⬝ᵥ V' = 0 := by rw [k2KarQuad_dot_eq_of_padMat hm hm', hd]
  obtain ⟨g₃, k, l, hkl, c₃, _, rfl⟩ := h₃
  obtain ⟨g₄, i, j, hij, c₄, _, rfl⟩ := h₄
  exact ⟨M', hM, c, w₁ * w₂, g₃, g₄, V', W', k, l, hkl, c₃, i, j, hij, c₄, hs', hm', hd', he⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_datumCheap_of_factor

/-- **Pair `(1,2)`.** -/
theorem k2KarQuadSt_datumCheap_of_pair12 (hs : s ≠ 0) {M : ℕ}
    {z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (h₁ : z₁ ∈ k2KarRel_gens s M) (h₂ : z₂ ∈ k2KarRel_gens s M)
    (h₃ : z₃ ∈ k2KarRel_gens s M) (h₄ : z₄ ∈ k2KarRel_gens s M)
    (hp : k2KarQuad_PairRankOne (z₁ * z₂)) : k2KarQuadSt_DatumCheap (z₁ * z₂ * z₃ * z₄) := by
  refine k2KarQuadSt_datumCheap_of_factor hs (le_refl M) 1 h₁ h₂ h₃ h₄ ?_ hp
  rw [k2KarQuadSt_indexMap_refl]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_datumCheap_of_pair12

/-- **Pair `(2,3)`**, by rotation `z₂ z₃ z₄ z₁ = z₁⁻¹ (z₁ z₂ z₃ z₄) z₁`. -/
theorem k2KarQuadSt_datumCheap_of_pair23 (hs : s ≠ 0) {M : ℕ}
    {z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (h₁ : z₁ ∈ k2KarRel_gens s M) (h₂ : z₂ ∈ k2KarRel_gens s M)
    (h₃ : z₃ ∈ k2KarRel_gens s M) (h₄ : z₄ ∈ k2KarRel_gens s M)
    (hp : k2KarQuad_PairRankOne (z₂ * z₃)) : k2KarQuadSt_DatumCheap (z₁ * z₂ * z₃ * z₄) := by
  refine k2KarQuadSt_datumCheap_of_factor hs (le_refl M) z₁⁻¹ h₂ h₃ h₄ h₁ ?_ hp
  rw [k2KarQuadSt_indexMap_refl]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_datumCheap_of_pair23

/-- **Pair `(1,3)`** (new): with `b = z₁ z₂ z₁⁻¹`, `z₁ z₂ z₃ z₄ = b z₁ z₃ z₄`, so
`b⁻¹ (z₁ z₂ z₃ z₄) b = z₁ z₃ z₄ b`. -/
theorem k2KarQuadSt_datumCheap_of_pair13 (hs : s ≠ 0) {M : ℕ}
    {z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (h₁ : z₁ ∈ k2KarRel_gens s M) (h₂ : z₂ ∈ k2KarRel_gens s M)
    (h₃ : z₃ ∈ k2KarRel_gens s M) (h₄ : z₄ ∈ k2KarRel_gens s M)
    (hp : k2KarQuad_PairRankOne (z₁ * z₃)) : k2KarQuadSt_DatumCheap (z₁ * z₂ * z₃ * z₄) := by
  refine k2KarQuadSt_datumCheap_of_factor hs (le_refl M) (z₁ * z₂ * z₁⁻¹)⁻¹ h₁ h₃ h₄
    (k2KarQuadRel_gens_conj z₁ h₂) ?_ hp
  rw [k2KarQuadSt_indexMap_refl]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_datumCheap_of_pair13

/-- **Pair `(2,4)`** (new): with `c' = z₂ z₃ z₂⁻¹`, `z₁ z₂ z₃ z₄ = z₁ c' z₂ z₄`, so
`(z₁ c')⁻¹ (z₁ z₂ z₃ z₄) (z₁ c') = z₂ z₄ z₁ c'`. -/
theorem k2KarQuadSt_datumCheap_of_pair24 (hs : s ≠ 0) {M : ℕ}
    {z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (h₁ : z₁ ∈ k2KarRel_gens s M) (h₂ : z₂ ∈ k2KarRel_gens s M)
    (h₃ : z₃ ∈ k2KarRel_gens s M) (h₄ : z₄ ∈ k2KarRel_gens s M)
    (hp : k2KarQuad_PairRankOne (z₂ * z₄)) : k2KarQuadSt_DatumCheap (z₁ * z₂ * z₃ * z₄) := by
  refine k2KarQuadSt_datumCheap_of_factor hs (le_refl M) (z₁ * (z₂ * z₃ * z₂⁻¹))⁻¹ h₂ h₄ h₁
    (k2KarQuadRel_gens_conj z₂ h₃) ?_ hp
  rw [k2KarQuadSt_indexMap_refl]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadSt_datumCheap_of_pair24

end KarQuadStCheap

end GroupApproximation.BooneHigman.Metabelian.ElemFP
