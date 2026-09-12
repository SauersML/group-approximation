import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationShort
import GroupApproximation.GroupTheory.HigmanThompson.RstabGerms
import GroupApproximation.Meta.AxiomGuard

/-!
# Lemma 4.6, Case 1: `Υ_{Γ₂}(I)' ∩ Υ^c_{Γ₂}(J₀) = Υ_{Γ₂}(J₀)'`

Hyde–Lodha, §4.3: "define `Υ_G(I) = RStab_G(Int(I) + ℤ)` and
`Υ_G^c(I) = {f ∈ Υ_G(I) | inf(I)·f'_+ = sup(I)·f'_- = 1}`."

Proof of Lemma 4.6, Case 1 (`|I| < 1`, `I ⊂ (0, 1)`): "from Lemma 4.4,
`Υ_{Γ_n}(I)' ∩ Υ_{Γ_n}^c(J_0) = Υ_{Γ_n}(J_0)'`, since `Υ_{Γ_n}(L) = Rstab_{F_{η_n}}(L + ℤ)` for an interval
`L ⊂ [0,1]`.  Indeed, for any `k ∈ Υ_{Γ_n}(I)'`, there is an `n ∈ ℕ` such that
`f^{-n} k f^n ∈ Υ_{Γ_n}^c(J_0)`, and so `f^{-n} k f^n ∈ Υ_{Γ_n}(J_0)' = H'`."

* `upsilonc Γ c d`: `Υ_Γ^c([c, d])`.  For these piecewise linear maps, slope `1` at `c` and at `d` means
  being the identity near `c + ℤ` and `d + ℤ`, so the support lies in `(c + δ, d - δ) + ℤ`.
* `commutator_upsilon_gammaTwo_eq_map`: in the unit frame, `Υ_{Γ₂}([a, b])'` is the periodic copy of
  `Rstab_{F_6}([a, b])'` (from `upsilon_gammaTwo_eq_map`).
* `upsilon_commutator_inter_upsilonc`: Lemma 4.4 (`rstab_commutator_inter_rstabc`) carried through `perHom`.
* `pow_conj_mem_commutator_upsilon`: the last sentence.  Permutations here compose right to left, so
  the paper's `f^{-n} k f^n` is `f ^ n * k * (f ^ n)⁻¹`.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

/-- **`Υ_Γ^c([c, d])`**: elements of `Γ` supported in `(c + δ, d - δ) + ℤ` for some `δ > 0`. -/
def upsilonc (Γ : Subgroup (Equiv.Perm ℚ)) (c d : ℚ) : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ Γ ∧ ∃ δ : ℚ, 0 < δ ∧ SupportedIn f (perIoo (c + δ) (d - δ))}
  one_mem' := ⟨one_mem Γ, 1, one_pos, supportedIn_one _⟩
  mul_mem' := by
    rintro f g ⟨hf, δf, hδf, hfs⟩ ⟨hg, δg, hδg, hgs⟩
    have hm1 := min_le_left δf δg
    have hm2 := min_le_right δf δg
    have hfs' : SupportedIn f (perIoo (c + min δf δg) (d - min δf δg)) :=
      hfs.mono (perIoo_mono (by linarith) (by linarith))
    have hgs' : SupportedIn g (perIoo (c + min δf δg) (d - min δf δg)) :=
      hgs.mono (perIoo_mono (by linarith) (by linarith))
    exact ⟨mul_mem hf hg, min δf δg, lt_min hδf hδg,
      (hfs'.mul hgs').mono (Set.union_subset subset_rfl subset_rfl)⟩
  inv_mem' := by
    rintro f ⟨hf, δ, hδ, hfs⟩
    exact ⟨inv_mem hf, δ, hδ, hfs.inv⟩

theorem mem_upsilonc {Γ : Subgroup (Equiv.Perm ℚ)} {c d : ℚ} {f : Equiv.Perm ℚ} :
    f ∈ upsilonc Γ c d ↔ f ∈ Γ ∧ ∃ δ : ℚ, 0 < δ ∧ SupportedIn f (perIoo (c + δ) (d - δ)) := Iff.rfl

/-! ## The unit frame -/

/-- `Υ_{Γ₂}([a, b])'` is the periodic copy of `Rstab_{F_6}([a, b])'`. -/
theorem commutator_upsilon_gammaTwo_eq_map {a b : ℚ} (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆ =
      (⁅rstab 4 a b, rstab 4 a b⁆.subgroupOf (compactF 4 1)).map (perHom 4) := by
  have hle : rstab 4 a b ≤ compactF 4 1 := rstab_le_compactF_one (m := 4) h0a.le hb1.le
  have hsub : ⁅(rstab 4 a b).subgroupOf (compactF 4 1), (rstab 4 a b).subgroupOf (compactF 4 1)⁆ =
      ⁅rstab 4 a b, rstab 4 a b⁆.subgroupOf (compactF 4 1) := by
    apply Subgroup.map_injective (f := (compactF 4 1).subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hle, inf_of_le_left ((commutator_le_self _).trans hle)]
  rw [upsilon_gammaTwo_eq_map h0a hab hb1, ← Subgroup.map_commutator, hsub]

theorem perHom_mem_upsilonc_of_rstabc {c d : ℚ} {x : ↥(compactF 4 1)}
    (hx : (x : Equiv.Perm ℚ) ∈ rstabc 4 c d) : perHom 4 x ∈ upsilonc gammaTwo c d := by
  obtain ⟨-, δ, hδ, h0, h1⟩ := hx
  refine mem_upsilonc.mpr ⟨perHom_mem_gammaTwo x, δ, hδ,
    (supportedIn_perHom 4 (f := x) (U := Set.Ioo (c + δ) (d - δ)) ?_).mono
      (perSet_Ioo_subset (c + δ) (d - δ))⟩
  intro t ht
  rcases le_or_gt t (c + δ) with h | h
  · exact h0 t h
  · exact h1 t (by by_contra hc; exact ht ⟨h, not_le.mp hc⟩)

theorem rstabc_of_perHom_mem_upsilonc {c d : ℚ} (h0c : 0 < c) (hd1 : d < 1) {x : ↥(compactF 4 1)}
    (hx : perHom 4 x ∈ upsilonc gammaTwo c d) : (x : Equiv.Perm ℚ) ∈ rstabc 4 c d := by
  obtain ⟨-, δ, hδ, hs⟩ := mem_upsilonc.mp hx
  have hfix : ∀ t : ℚ, t ≤ c + δ ∨ d - δ ≤ t → (x : Equiv.Perm ℚ) t = t := by
    intro t ht
    rcases le_or_gt t 0 with ht0 | ht0
    · exact compactF_fix_nonpos x.2 ht0
    rcases le_or_gt 1 t with ht1 | ht1
    · exact compactF_fix_one x.2 ht1
    rw [← perHom_apply_of_mem 4 x ht0.le ht1]
    exact hs t (not_mem_perIoo_of_unit (by linarith) (by linarith) ht0.le ht1 ht)
  exact ⟨⟨x.2.1, fun t ht => hfix t (Or.inl (by linarith)), fun t ht => hfix t (Or.inr (by linarith))⟩,
    δ, hδ, fun t ht => hfix t (Or.inl ht), fun t ht => hfix t (Or.inr ht)⟩

/-! ## Case 1 -/

/-- Commutators of `Υ_{Γ₂}([a, b])` have slope `1` at `a` and `b`. -/
theorem commutator_upsilon_le_upsilonc {a b : ℚ} (ha : ∃ M, a ∈ Grid 6 M) (hb : ∃ M, b ∈ Grid 6 M)
    (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆ ≤ upsilonc gammaTwo a b := by
  rw [commutator_upsilon_gammaTwo_eq_map h0a hab hb1]
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
  exact perHom_mem_upsilonc_of_rstabc (commutator_le_rstabc (m := 4) ha hb hx)

/-- **Hyde–Lodha, proof of Lemma 4.6, Case 1**: "`Υ_{Γ_n}(I)' ∩ Υ_{Γ_n}^c(J_0) = Υ_{Γ_n}(J_0)'`", for
`I = [a, b]` and `J₀ = [c, d]` with `0 < a < c < d < b < 1` in `ℤ[1/6]`. -/
theorem upsilon_commutator_inter_upsilonc {a b c d : ℚ} (ha : ∃ M, a ∈ Grid 6 M)
    (hb : ∃ M, b ∈ Grid 6 M) (hc : ∃ M, c ∈ Grid 6 M) (hd : ∃ M, d ∈ Grid 6 M)
    (h0a : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b) (hb1 : b < 1) :
    ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆ ⊓ upsilonc gammaTwo c d =
      ⁅upsilon gammaTwo c d, upsilon gammaTwo c d⁆ := by
  apply le_antisymm
  · rintro y ⟨hy1, hy2⟩
    rw [commutator_upsilon_gammaTwo_eq_map h0a (by linarith) hb1] at hy1
    obtain ⟨x, hx, rfl⟩ := hy1
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    have hxc := rstabc_of_perHom_mem_upsilonc (by linarith) (by linarith) hy2
    have hmem : (x : Equiv.Perm ℚ) ∈ ⁅rstab 4 c d, rstab 4 c d⁆ := by
      rw [← rstab_commutator_inter_rstabc 4 ha hb hc hd h0a hac hcd hdb hb1]
      exact Subgroup.mem_inf.mpr ⟨hx, hxc⟩
    rw [commutator_upsilon_gammaTwo_eq_map (by linarith) hcd (by linarith)]
    exact Subgroup.mem_map_of_mem (perHom 4) (Subgroup.mem_subgroupOf.mpr hmem)
  · have hmono : upsilon gammaTwo c d ≤ upsilon gammaTwo a b :=
      upsilon_mono le_rfl (perIoo_mono hac.le hdb.le)
    exact le_inf (Subgroup.commutator_mono hmono hmono)
      (commutator_upsilon_le_upsilonc hc hd (by linarith) hcd (by linarith))

/-- **Hyde–Lodha, proof of Lemma 4.6, Case 1**: "for any `k ∈ Υ_{Γ_n}(I)'`, there is an `n ∈ ℕ` such
that `f^{-n} k f^n ∈ Υ_{Γ_n}^c(J_0)`, and so `f^{-n} k f^n ∈ Υ_{Γ_n}(J_0)'`". -/
theorem pow_conj_mem_commutator_upsilon {a b c d : ℚ} (ha : ∃ M, a ∈ Grid 6 M)
    (hb : ∃ M, b ∈ Grid 6 M) (hc : ∃ M, c ∈ Grid 6 M) (hd : ∃ M, d ∈ Grid 6 M)
    (h0a : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b) (hb1 : b < 1)
    {f : Equiv.Perm ℚ} (hf : f ∈ upsilon gammaTwo a b) {k : Equiv.Perm ℚ}
    (hk : k ∈ ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆) {n : ℕ}
    (hn : f ^ n * k * (f ^ n)⁻¹ ∈ upsilonc gammaTwo c d) :
    f ^ n * k * (f ^ n)⁻¹ ∈ ⁅upsilon gammaTwo c d, upsilon gammaTwo c d⁆ := by
  have hfn : f ^ n ∈ upsilon gammaTwo a b := pow_mem hf n
  have hk' : k ∈ upsilon gammaTwo a b := commutator_le_self _ hk
  have e : f ^ n * k * (f ^ n)⁻¹ = ⁅f ^ n, k⁆ * k := by
    rw [commutatorElement_def, inv_mul_cancel_right]
  rw [← upsilon_commutator_inter_upsilonc ha hb hc hd h0a hac hcd hdb hb1]
  refine Subgroup.mem_inf.mpr ⟨?_, hn⟩
  rw [e]
  exact mul_mem (Subgroup.commutator_mem_commutator hfn hk') hk

#audit_axioms GroupApproximation.HydeLodha.commutator_upsilon_le_upsilonc
#audit_axioms GroupApproximation.HydeLodha.upsilon_commutator_inter_upsilonc
#audit_axioms GroupApproximation.HydeLodha.pow_conj_mem_commutator_upsilon

end HydeLodha
end GroupApproximation
