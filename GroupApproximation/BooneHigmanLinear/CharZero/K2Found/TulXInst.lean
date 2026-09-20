import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXNat
import GroupApproximation.BooneHigmanLinear.PaninAffine.TulX
import GroupApproximation.Meta.AxiomGuard

/-!
# An instance of `PaninAffine.TulX` from van der Kallen's elements (T 1.1–1.3, for F.4)

Let `r ≥ 5`. Suppose we have van der Kallen's elements `E B : VdK.Elements (Fin r) B` for every
ring `B`, local (`IsLocal`, vdK) and natural in ring maps (`EltNatural`). Then Tulenbaev's
`X_{v,w}(t) := Xa v w u`, for any `u` with `u v = t`, satisfies every field of k2-panin's
interface `PaninAffine.TulX r` (`tulX_of_elements`). Both hypotheses are k2-vdk's exports for its
construction of the elements.

Admissible rows `w ∈ I(v) · v^⊥` lie in the span of the two-zero rows `⊥ v`, via the canonical
pieces (`dec_of_adm`). They are stable under `π(γ)` (`adm_conj`) and under ring maps
(`adm_map`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (Elements)
open GroupApproximation.BooneHigmanLinear.PaninAffine (TulX AdmRow coordIdeal orthSub pMat)

variable {r : ℕ}

theorem exists_row_of_mem {B : Type*} [CommRing B] {v : Fin r → B} {t : B}
    (ht : t ∈ coordIdeal v) : ∃ u : Fin r → B, u ⬝ᵥ v = t :=
  Ideal.mem_span_range_iff_exists_fun.mp ht

theorem mem_of_row {B : Type*} [CommRing B] (u v : Fin r → B) : u ⬝ᵥ v ∈ coordIdeal v :=
  Ideal.mem_span_range_iff_exists_fun.mpr ⟨u, rfl⟩

theorem perp_of_adm {B : Type*} [CommRing B] {v w : Fin r → B} (hw : AdmRow v w) :
    w ⬝ᵥ v = 0 :=
  Submodule.smul_le_right hw

/-- Admissible rows are sums of two-zero rows `⊥ v`. -/
theorem dec_of_adm (h4 : 4 ≤ r) {B : Type*} [CommRing B] {v w : Fin r → B} (hw : AdmRow v w) :
    w ∈ Submodule.span B (two0 v) := by
  refine Submodule.smul_induction_on hw (fun c hc n hn => ?_)
    (fun x y hx hy => Submodule.add_mem _ hx hy)
  obtain ⟨u, rfl⟩ := exists_row_of_mem hc
  rw [← pc_sum_all u (show n ⬝ᵥ v = 0 from hn)]
  exact Submodule.sum_mem _ fun pq _ => Submodule.subset_span
    ⟨pc_dot v n u pq.1 pq.2, pc_twoZ (by rw [Fintype.card_fin]; exact h4) v n u pq.1 pq.2⟩

theorem adm_conj {B : Type*} [CommRing B] (γ : SteinbergGroup (Fin r) B) {v w : Fin r → B}
    (hw : AdmRow v w) : AdmRow (pm γ *ᵥ v) (w ᵥ* pm γ⁻¹) := by
  refine Submodule.smul_induction_on (p := fun w => AdmRow (pm γ *ᵥ v) (w ᵥ* pm γ⁻¹)) hw
    (fun c hc n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨u, rfl⟩ := exists_row_of_mem hc
    change AdmRow _ (((u ⬝ᵥ v) • n) ᵥ* pm γ⁻¹)
    rw [smul_vecMul, ← dot_transform γ u v]
    exact PaninAffine.admRow_smul (mem_of_row _ _)
      (show (n ᵥ* pm γ⁻¹) ⬝ᵥ (pm γ *ᵥ v) = 0 by rw [dot_transform]; exact hn)
  · change AdmRow _ ((x + y) ᵥ* pm γ⁻¹)
    rw [add_vecMul]
    exact Submodule.add_mem _ hx hy

theorem adm_map {B C : Type*} [CommRing B] [CommRing C] (f : B →+* C) {v w : Fin r → B}
    (hw : AdmRow v w) : AdmRow (f ∘ v) (f ∘ w) := by
  refine Submodule.smul_induction_on (p := fun w => AdmRow (f ∘ v) (f ∘ w)) hw
    (fun c hc n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨u, rfl⟩ := exists_row_of_mem hc
    change AdmRow _ (f ∘ ((u ⬝ᵥ v) • n))
    rw [comp_smul, RingHom.map_dotProduct]
    exact PaninAffine.admRow_smul (mem_of_row _ _)
      (show (f ∘ n) ⬝ᵥ (f ∘ v) = 0 by rw [← RingHom.map_dotProduct, show n ⬝ᵥ v = 0 from hn, map_zero])
  · change AdmRow _ (f ∘ (x + y))
    rw [comp_add]
    exact Submodule.add_mem _ hx hy

theorem card_fin_ge {k : ℕ} (h : k ≤ r) : k ≤ Fintype.card (Fin r) := by
  rw [Fintype.card_fin]
  exact h

theorem pMat_eq_pm {B : Type*} [CommRing B] (γ : SteinbergGroup (Fin r) B) : pMat γ = pm γ :=
  rfl

/-- T 1.3(b) for admissible rows: `γ X_{v,w}(t) γ⁻¹ = X_{γv, wγ⁻¹}(t)`. -/
theorem Xa_conj_adm {B : Type*} [CommRing B] (hX : Elements (Fin r) B) [Fact (IsLocal hX)]
    (h5 : 5 ≤ Fintype.card (Fin r)) (γ : SteinbergGroup (Fin r) B) {v w : Fin r → B}
    (hw : AdmRow v w) (u : Fin r → B) :
    γ * Xa hX (Nat.le_of_succ_le h5) v w u * γ⁻¹ =
      Xa hX (Nat.le_of_succ_le h5) (pm γ *ᵥ v) (w ᵥ* pm γ⁻¹) (u ᵥ* pm γ⁻¹) := by
  refine Submodule.smul_induction_on (p := fun w => γ * Xa hX (Nat.le_of_succ_le h5) v w u * γ⁻¹ =
      Xa hX (Nat.le_of_succ_le h5) (pm γ *ᵥ v) (w ᵥ* pm γ⁻¹) (u ᵥ* pm γ⁻¹)) hw
    (fun c hc n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨ub, rfl⟩ := exists_row_of_mem hc
    change γ * Xa hX _ v ((ub ⬝ᵥ v) • n) u * γ⁻¹ =
      Xa hX _ (pm γ *ᵥ v) (((ub ⬝ᵥ v) • n) ᵥ* pm γ⁻¹) (u ᵥ* pm γ⁻¹)
    rw [Xa_conj hX h5 γ v n u ub hn, smul_vecMul]
  · have hx' : γ * Xa hX (Nat.le_of_succ_le h5) v x u * γ⁻¹ =
        Xa hX (Nat.le_of_succ_le h5) (pm γ *ᵥ v) (x ᵥ* pm γ⁻¹) (u ᵥ* pm γ⁻¹) := hx
    have hy' : γ * Xa hX (Nat.le_of_succ_le h5) v y u * γ⁻¹ =
        Xa hX (Nat.le_of_succ_le h5) (pm γ *ᵥ v) (y ᵥ* pm γ⁻¹) (u ᵥ* pm γ⁻¹) := hy
    change γ * Xa hX _ v (x + y) u * γ⁻¹ =
      Xa hX _ (pm γ *ᵥ v) ((x + y) ᵥ* pm γ⁻¹) (u ᵥ* pm γ⁻¹)
    rw [Xa_add, add_vecMul, Xa_add, ← hx', ← hy']
    group

#audit_axioms Xa_conj_adm

section Inst

variable (E : ∀ (B : Type) [CommRing B], Elements (Fin r) B)
  [hL : ∀ (B : Type) [CommRing B], Fact (IsLocal (E B))]

open Classical in
/-- Tulenbaev's `X_{v,w}(t)`: `Xa v w u` for some `u` with `u v = t` (`1` if there is none). -/
noncomputable def tX (h4 : 4 ≤ Fintype.card (Fin r)) {B : Type} [CommRing B]
    (v w : Fin r → B) (t : B) : SteinbergGroup (Fin r) B :=
  if h : ∃ u : Fin r → B, u ⬝ᵥ v = t then Xa (E B) h4 v w h.choose else 1

theorem tX_eq (h4 : 4 ≤ Fintype.card (Fin r)) {B : Type} [CommRing B] {v w : Fin r → B}
    (hw : w ∈ Submodule.span B (two0 v)) {u : Fin r → B} {t : B} (hu : u ⬝ᵥ v = t) :
    tX E h4 v w t = Xa (E B) h4 v w u := by
  have h : ∃ u : Fin r → B, u ⬝ᵥ v = t := ⟨u, hu⟩
  rw [tX, dif_pos h]
  exact Xa_indep (E B) h4 hw (h.choose_spec.trans hu.symm)

#audit_axioms tX_eq

/-- **`PaninAffine.TulX r` from van der Kallen's elements** (T 1.1–1.3), for `r ≥ 5`: the
elements must be local and natural. -/
noncomputable def tulX_of_elements
    (hnat : ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), EltNatural (E B) (E C) f)
    (h5 : 5 ≤ r) : TulX r where
  X := tX E (card_fin_ge (by omega))
  nat := by
    intro B C _ _ f v w t hw ht
    obtain ⟨u, rfl⟩ := exists_row_of_mem ht
    rw [tX_eq E _ (dec_of_adm (by omega) hw) rfl, Xa_natural (E B) (E C) f (hnat B C f),
      tX_eq E _ (dec_of_adm (by omega) (adm_map f hw)) (RingHom.map_dotProduct f u v).symm]
  add := by
    intro B _ v w t t' hw ht ht'
    obtain ⟨u, rfl⟩ := exists_row_of_mem ht
    obtain ⟨u', rfl⟩ := exists_row_of_mem ht'
    have hd := dec_of_adm (by omega) hw
    rw [tX_eq E _ hd rfl, tX_eq E _ hd rfl, tX_eq E _ hd (add_dotProduct u u' v),
      Xa_add_u (E B) _ hd]
  rowAdd := by
    intro B _ v w w' t hw hw' ht
    obtain ⟨u, rfl⟩ := exists_row_of_mem ht
    rw [tX_eq E _ (dec_of_adm (by omega) hw) rfl, tX_eq E _ (dec_of_adm (by omega) hw') rfl,
      tX_eq E _ (dec_of_adm (by omega) (Submodule.add_mem _ hw hw')) rfl, Xa_add]
  smulRow := by
    intro B _ v w c t hw ht
    obtain ⟨u, rfl⟩ := exists_row_of_mem ht
    have hd := dec_of_adm (by omega) hw
    rw [tX_eq E _ (Submodule.smul_mem _ c hd) rfl,
      tX_eq E _ hd (show (c • u) ⬝ᵥ v = c * (u ⬝ᵥ v) by rw [smul_dotProduct, smul_eq_mul]),
      Xa_smul_u]
  smulCol := by
    intro B _ v w c t hw ht
    obtain ⟨u, rfl⟩ := exists_row_of_mem ht
    have hd := dec_of_adm (by omega) hw
    have hd' : w ∈ Submodule.span B (two0 (c • v)) :=
      Submodule.span_mono (show two0 v ⊆ two0 (c • v) from
        fun x hx => ⟨dot_smul_zero c hx.1, hx.2⟩) hd
    have hcu : ((c * c) • u) ⬝ᵥ v = c * (u ⬝ᵥ (c • v)) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [tX_eq E _ hd' rfl, tX_eq E _ hd hcu, Xa_smul_col (E B) _ hd c hcu]
  colAdd := by
    intro B _ v v' w c t hw ht htc ht'
    obtain ⟨u, hu⟩ := exists_row_of_mem ht'
    obtain ⟨u₁, hu₁⟩ := exists_row_of_mem ht
    obtain ⟨u₂, hu₂⟩ := exists_row_of_mem htc
    have hd0 : w ∈ Submodule.span B (two0 (v + c • v')) :=
      Submodule.span_mono (show TwoZero.twoZeroSet v v' ⊆ two0 (v + c • v') from
        fun x hx => ⟨dot_add hx.1 (dot_smul_zero c hx.2.1), hx.2.2⟩) hw
    have hd1 : w ∈ Submodule.span B (two0 v) :=
      Submodule.span_mono (show TwoZero.twoZeroSet v v' ⊆ two0 v from
        fun x hx => ⟨hx.1, hx.2.2⟩) hw
    have hd2 : w ∈ Submodule.span B (two0 v') :=
      Submodule.span_mono (show TwoZero.twoZeroSet v v' ⊆ two0 v' from
        fun x hx => ⟨hx.2.1, hx.2.2⟩) hw
    rw [tX_eq E _ hd0 hu, tX_eq E _ hd1 hu₁, tX_eq E _ hd2 hu₂]
    exact Xa_col_add (E B) _ hw c u u₁ u₂ (hu₁.trans hu.symm) (hu₂.trans (by rw [hu]))
  conj := by
    intro B _ v w t hw ht γ
    obtain ⟨u, rfl⟩ := exists_row_of_mem ht
    rw [pMat_eq_pm, pMat_eq_pm, tX_eq E _ (dec_of_adm (by omega) hw) rfl,
      Xa_conj_adm (E B) (card_fin_ge h5) γ hw u,
      tX_eq E _ (dec_of_adm (by omega) (adm_conj γ hw)) (dot_transform γ u v)]
  proj := by
    intro B _ v w t hw ht
    obtain ⟨u, rfl⟩ := exists_row_of_mem ht
    rw [tX_eq E _ (dec_of_adm (by omega) hw) rfl, pMat_eq_pm, pm_Xa (E B) _ u (perp_of_adm hw)]
  single := by
    intro B _ k l hkl t
    obtain ⟨p, q, hpq, hpl, -, hql, -⟩ := exists_two_ne (card_fin_ge (by omega)) l l
    have hu : (t • Pi.single k (1 : B)) ⬝ᵥ Pi.single k 1 = t := by
      rw [smul_dotProduct, single_one_dotProduct, Pi.single_eq_same, smul_eq_mul, mul_one]
    have hd : Pi.single l (1 : B) ∈ Submodule.span B (two0 (Pi.single k 1)) :=
      Submodule.subset_span ⟨by rw [dotProduct_single_one, Pi.single_eq_of_ne hkl],
        ⟨p, q, hpq, Pi.single_eq_of_ne hpl 1, Pi.single_eq_of_ne hql 1⟩⟩
    rw [tX_eq E _ hd hu, Xa_single (E B) _ hkl, hu]

end Inst

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
