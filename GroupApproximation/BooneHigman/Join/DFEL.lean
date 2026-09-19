import GroupApproximation.BooneHigman.Join.DCode
import GroupApproximation.BooneHigman.Join.DGood

/-!
# The expansion lemma over `Fin (n + 2)` (lane bh-pal-met-join)

`DFELAt L σ d`: `σ = f · ρ`, where `f ∈ PhiD n` and `ρ ∈ jH (exF L d)`, and `f` carries
`exF L d` rigidly onto `exF L d'` for some `d' ∈ L`.

* `dfelAt_mul`: the property is multiplicative (`rcl_H`).
* `dfel_adj`: it holds for a letter `ℓ(u, v)` of adjacent words `u`, `v` of `L`, with
  `f = P(u, v)` and `ρ = ℓ(v t, u) · (v K₀)⁻¹` (`Prot_alt`), or the inverse form.
* `letters_mem`: in a chain of adjacent words, every letter is a product of conjugates of
  adjacent letters.
* `dfel`: every `σ ∈ jH L` has the property at every word of `L`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- The expansion property at the word `d` of `L`. -/
def DFELAt (L : List (List (Fin (n + 2)))) (σ : higmanVCCommon_Q (n + 2))
    (d : List (Fin (n + 2))) : Prop :=
  ∃ d' ∈ L, ∃ f ∈ PhiD n, ∃ ρ ∈ jH (n + 2) (exF L d), σ = f * ρ ∧
    ∀ c' ∈ exF L d', ∃ c ∈ exF L d, MapsCone (jperm (n + 2) f) c c'

#audit_axioms GroupApproximation.BooneHigman.Join.DFELAt

theorem dfelAt_of_mem {L : List (List (Fin (n + 2)))} {σ : higmanVCCommon_Q (n + 2)}
    {d : List (Fin (n + 2))} (hd : d ∈ L) (hσ : σ ∈ jH (n + 2) (exF L d)) : DFELAt L σ d :=
  ⟨d, hd, 1, (PhiD n).one_mem, σ, hσ, (one_mul σ).symm, fun c' hc' => ⟨c', hc', dmc_one c'⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Join.dfelAt_of_mem

/-- **Multiplicativity.** -/
theorem dfelAt_mul {L : List (List (Fin (n + 2)))} (hL : IsCode n L) {σ₁ σ₂ : higmanVCCommon_Q (n + 2)}
    {d : List (Fin (n + 2))} (h₂ : DFELAt L σ₂ d) (h₁ : ∀ e ∈ L, DFELAt L σ₁ e) :
    DFELAt L (σ₁ * σ₂) d := by
  obtain ⟨d', hd', f₂, hf₂, ρ₂, hρ₂, e₂, hm₂⟩ := h₂
  obtain ⟨d'', hd'', f₁, hf₁, ρ₁, hρ₁, e₁, hm₁⟩ := h₁ d' hd'
  refine ⟨d'', hd'', f₁ * f₂, (PhiD n).mul_mem hf₁ hf₂, f₂⁻¹ * ρ₁ * f₂ * ρ₂, ?_, ?_, ?_⟩
  · refine (jH (n + 2) _).mul_mem ?_ hρ₂
    have h := rcl_H (dn2 n) (exF_isAC hL hd') f₂⁻¹ (C' := exF L d) ?_ hρ₁
    · rwa [inv_inv] at h
    · intro c hc
      obtain ⟨c₀, hc₀, hm⟩ := hm₂ c hc
      exact ⟨c₀, hc₀, dmc_inv hm⟩
  · rw [e₁, e₂]
    group
  · intro c'' hc''
    obtain ⟨c', hc', hm'⟩ := hm₁ c'' hc''
    obtain ⟨c, hc, hm⟩ := hm₂ c' hc'
    exact ⟨c, hc, dmc_mul hm hm'⟩

#audit_axioms GroupApproximation.BooneHigman.Join.dfelAt_mul

theorem DAdj.inc {u v : List (Fin (n + 2))} (h : DAdj u v) : Inc u v := by
  obtain ⟨w, i, a, b, hi, rfl, rfl⟩ := h
  have hne : fc n i ≠ fc n (i + 1) := fc_ne (by omega) (by omega) (by omega)
  exact ⟨dinc_cons w hne _ _, dinc_cons w hne.symm _ _⟩

#audit_axioms GroupApproximation.BooneHigman.Join.DAdj.inc

theorem DAdj.mem {u v : List (Fin (n + 2))} (h : DAdj u v) : Prot u v ∈ PhiD n := by
  obtain ⟨w, i, a, b, hi, rfl, rfl⟩ := h
  exact cross_mem w hi a b

#audit_axioms GroupApproximation.BooneHigman.Join.DAdj.mem

/-- The cone maps of `P(u, v)` from `exF L v` to `exF L u`, in both directions. -/
theorem prot_maps {L : List (List (Fin (n + 2)))} (hL : IsCode n L) {u v : List (Fin (n + 2))}
    (hu : u ∈ L) (hv : v ∈ L) (h : Inc u v) :
    (∀ c ∈ exF L v, ∃ c' ∈ exF L u, MapsCone (jperm (n + 2) (Prot u v)) c c') ∧
    (∀ c' ∈ exF L u, ∃ c ∈ exF L v, MapsCone (jperm (n + 2) (Prot u v)) c c') := by
  have huv : u ≠ v := fun e => by
    subst e
    exact h.1 (List.prefix_refl _)
  have hfix : ∀ c ∈ L, c ≠ u → c ≠ v → MapsCone (jperm (n + 2) (Prot u v)) c c := by
    intro c hc h1 h2
    have i1 := hL.inc hc hu h1
    have i2 := hL.inc hc hv h2
    exact Prot_fix h.1 h.2 i1.2 i1.1 i2.2 i2.1
  refine ⟨fun c hc => ?_, fun c' hc' => ?_⟩
  · rcases mem_exF.mp hc with ⟨hc, hcv⟩ | ⟨a, rfl⟩
    · by_cases hcu : c = u
      · refine ⟨u ++ [fc n 0], mem_exF.mpr (Or.inr ⟨_, rfl⟩), ?_⟩
        rw [hcu]
        exact Prot_x h.1 h.2
      · exact ⟨c, mem_exF.mpr (Or.inl ⟨hc, hcu⟩), hfix c hc hcu hcv⟩
    · rcases Nat.lt_or_ge a.val (n + 1) with ha | ha
      · refine ⟨u ++ [fc n (a.val + 1)], mem_exF.mpr (Or.inr ⟨_, rfl⟩), ?_⟩
        have hp := Prot_y h.1 h.2 ha
        rwa [fc_val] at hp
      · have e : a = tl n := Fin.ext (by
          rw [fc_val_of_lt (n := n) (i := n + 1) (by omega)]
          have := a.isLt
          omega)
        subst e
        exact ⟨v, mem_exF.mpr (Or.inl ⟨hv, huv.symm⟩), Prot_yt h.1 h.2⟩
  · rcases mem_exF.mp hc' with ⟨hc, hcu⟩ | ⟨a, rfl⟩
    · by_cases hcv : c' = v
      · refine ⟨v ++ [tl n], mem_exF.mpr (Or.inr ⟨_, rfl⟩), ?_⟩
        rw [hcv]
        exact Prot_yt h.1 h.2
      · exact ⟨c', mem_exF.mpr (Or.inl ⟨hc, hcv⟩), hfix c' hc hcu hcv⟩
    · rcases Nat.eq_zero_or_pos a.val with ha | ha
      · have e : a = fc n 0 := Fin.ext (by rw [ha, fc_val_of_lt (n := n) (i := 0) (by omega)])
        subst e
        exact ⟨u, mem_exF.mpr (Or.inl ⟨hu, huv⟩), Prot_x h.1 h.2⟩
      · refine ⟨v ++ [fc n (a.val - 1)], mem_exF.mpr (Or.inr ⟨_, rfl⟩), ?_⟩
        have hp := Prot_y h.1 h.2 (i := a.val - 1) (by have := a.isLt; omega)
        rwa [show a.val - 1 + 1 = a.val by omega, fc_val] at hp

#audit_axioms GroupApproximation.BooneHigman.Join.prot_maps

/-- `ℓ(u, v) = P(u, v) · ρ` with `ρ` on the words of `exF L v`. -/
theorem jL_eq_prot {L : List (List (Fin (n + 2)))} {u v : List (Fin (n + 2))} (hu : u ∈ L)
    (h : Inc u v) : ∃ ρ ∈ jH (n + 2) (exF L v), jL u v = Prot u v * ρ := by
  have huv : u ≠ v := fun e => by
    subst e
    exact h.1 (List.prefix_refl _)
  refine ⟨jL (v ++ [tl n]) u * (jPhi (n + 2) v (K0 n))⁻¹, (jH (n + 2) _).mul_mem
    (jL_mem_jH (mem_exF.mpr (Or.inr ⟨_, rfl⟩)) (mem_exF.mpr (Or.inl ⟨hu, huv⟩)))
    ((jH (n + 2) _).inv_mem (jH_mono ?_ (jPhi_mem_jH v (Rch_mem n (n + 1))))), ?_⟩
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact mem_exF.mpr (Or.inr ⟨a, rfl⟩)
  · rw [Prot_alt h.1 h.2]
    have hs := jL_sq (v ++ [tl n]) u
    have hs2 := jL_sq u v
    calc jL u v = jL u v * jPhi (n + 2) v (K0 n) * (jL (v ++ [tl n]) u * jL (v ++ [tl n]) u) *
          (jPhi (n + 2) v (K0 n))⁻¹ := by rw [hs]; group
      _ = _ := by group

#audit_axioms GroupApproximation.BooneHigman.Join.jL_eq_prot

/-- **The expansion property for adjacent letters.** -/
theorem dfel_adj {L : List (List (Fin (n + 2)))} (hL : IsCode n L) {u v : List (Fin (n + 2))}
    (hu : u ∈ L) (hv : v ∈ L) (h : DAdj u v) {d : List (Fin (n + 2))} (hd : d ∈ L) :
    DFELAt L (jL u v) d := by
  have hi := h.inc
  obtain ⟨hfw, hbw⟩ := prot_maps hL hu hv hi
  obtain ⟨ρ, hρ, e⟩ := jL_eq_prot (L := L) hu hi
  by_cases hdv : d = v
  · rw [hdv]
    exact ⟨u, hu, Prot u v, h.mem, ρ, hρ, e, hbw⟩
  by_cases hdu : d = u
  · rw [hdu]
    refine ⟨v, hv, (Prot u v)⁻¹, (PhiD n).inv_mem h.mem, Prot u v * ρ⁻¹ * (Prot u v)⁻¹, ?_, ?_, ?_⟩
    · exact rcl_H (dn2 n) (exF_isAC hL hv) (Prot u v) hfw ((jH (n + 2) _).inv_mem hρ)
    · rw [← jL_inv, e]
      group
    · intro c' hc'
      obtain ⟨c, hc, hm⟩ := hfw c' hc'
      exact ⟨c, hc, dmc_inv hm⟩
  · refine dfelAt_of_mem hd (jL_mem_jH (mem_exF.mpr (Or.inl ⟨hu, fun e => hdu e.symm⟩))
      (mem_exF.mpr (Or.inl ⟨hv, fun e => hdv e.symm⟩)))

#audit_axioms GroupApproximation.BooneHigman.Join.dfel_adj

/-- In a chain of adjacent, pairwise incomparable words, every letter lies in a set that
contains `1` and the adjacent letters and is closed under products. -/
theorem letters_mem (S : Set (higmanVCCommon_Q (n + 2))) (h1 : (1 : higmanVCCommon_Q (n + 2)) ∈ S)
    (hmul : ∀ a b, a ∈ S → b ∈ S → a * b ∈ S) :
    ∀ L : List (List (Fin (n + 2))), L.Pairwise Inc → L.IsChain DAdj →
      (∀ u v, u ∈ L → v ∈ L → DAdj u v → jL u v ∈ S) → ∀ u ∈ L, ∀ v ∈ L, jL u v ∈ S
  | [], _, _, _ => fun u hu => by simp at hu
  | a :: L, hp, hc, hadj => by
    rw [List.pairwise_cons] at hp
    rw [List.isChain_cons] at hc
    have ih := letters_mem S h1 hmul L hp.2 hc.2
      (fun u v hu hv => hadj u v (List.mem_cons_of_mem a hu) (List.mem_cons_of_mem a hv))
    have key : ∀ v ∈ L, jL a v ∈ S := by
      intro v hv
      cases L with
      | nil => simp at hv
      | cons b L' =>
        have hab : DAdj a b := hc.1 b rfl
        have hlab := hadj a b List.mem_cons_self (List.mem_cons_of_mem a List.mem_cons_self) hab
        by_cases hvb : v = b
        · rw [hvb]
          exact hlab
        · have iab := hp.1 b List.mem_cons_self
          have iav := hp.1 v hv
          have ibv := pairwise_inc_mem hp.2 List.mem_cons_self hv (Ne.symm hvb)
          have hr := rcl (dn2 n) (jL a b) ibv.1 ibv.2 (dmc_jL_right iab.1 iab.2)
            (dmc_jL_fix iab.1 iab.2 iav.1 iav.2 ibv.1 ibv.2)
          rw [jL_inv] at hr
          rw [← hr]
          exact hmul _ _ (hmul _ _ hlab (ih b List.mem_cons_self v hv)) hlab
    intro u hu v hv
    rcases List.mem_cons.mp hu with hu' | hu' <;> rcases List.mem_cons.mp hv with hv' | hv'
    · rw [hu', hv', jL_self]
      exact h1
    · rw [hu']
      exact key v hv'
    · rw [hv', jL_symmD (dn2 n) (hp.1 u hu').2 (hp.1 u hu').1]
      exact key u hu'
    · exact ih u hu' v hv'

#audit_axioms GroupApproximation.BooneHigman.Join.letters_mem

/-- Monoid induction on an antichain subgroup: letters are involutions. -/
theorem jH_induction_monD {d : ℕ} {C : Finset (List (Fin d))} {P : higmanVCCommon_Q d → Prop}
    (h1 : P 1) (hL : ∀ x ∈ C, ∀ y ∈ C, P (jL x y)) (hmul : ∀ a b, P a → P b → P (a * b))
    {σ : higmanVCCommon_Q d} (hσ : σ ∈ jH d C) : P σ := by
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hσ
  clear hσ
  induction r using FreeGroup.induction_on with
  | C1 => simpa using h1
  | of p =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    show P (higmanVCCommon_mk d (higmanVCAll_iota C (FreeGroup.of _)))
    rw [higmanVCAll_iota_of]
    exact hL x hx y hy
  | inv_of p _ =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    show P (higmanVCCommon_mk d (higmanVCAll_iota C (FreeGroup.of _)⁻¹))
    rw [map_inv, map_inv, higmanVCAll_iota_of]
    show P (jL x y)⁻¹
    rw [jL_inv]
    exact hL x hx y hy
  | mul a b iha ihb =>
    simp only [MonoidHom.comp_apply, map_mul] at iha ihb ⊢
    exact hmul _ _ iha ihb

#audit_axioms GroupApproximation.BooneHigman.Join.jH_induction_monD

/-- **The expansion lemma**: every element of `jH L` has the property at every word of `L`. -/
theorem dfel {L : List (List (Fin (n + 2)))} (hL : IsCode n L) {σ : higmanVCCommon_Q (n + 2)}
    (hσ : σ ∈ jH (n + 2) L.toFinset) : ∀ d ∈ L, DFELAt L σ d := by
  let S : Set (higmanVCCommon_Q (n + 2)) := {s | ∀ d ∈ L, DFELAt L s d}
  have h1 : (1 : higmanVCCommon_Q (n + 2)) ∈ S := show ∀ d ∈ L, DFELAt L 1 d from
    fun d hd => dfelAt_of_mem hd (jH (n + 2) _).one_mem
  have hmul : ∀ a b, a ∈ S → b ∈ S → a * b ∈ S := fun a b ha hb =>
    show ∀ d ∈ L, DFELAt L (a * b) d from fun d hd => dfelAt_mul hL (hb d hd) ha
  have hlet := letters_mem S h1 hmul L hL.pairwise hL.chain
    (fun u v hu hv h => show ∀ d ∈ L, DFELAt L (jL u v) d from fun d hd => dfel_adj hL hu hv h hd)
  exact jH_induction_monD (P := fun s => s ∈ S) h1
    (fun x hx y hy => hlet x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy)) hmul hσ

#audit_axioms GroupApproximation.BooneHigman.Join.dfel

end GroupApproximation.BooneHigman.Join
