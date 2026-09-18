import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnGraded.Admissible
import GroupApproximation.Meta.AxiomGuard

/-!
# Potential corner maps act trivially on stable `K₂(C_2(𝔽₂))` (lane sk-lv-04)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  For a potential
`m : Fin n → ℕ`, let `cornerMap σ^m τ^m` be the endomorphism
`x_{ij}(a) ↦ x_{ij}(x₀^{m i} a y₀^{m j})` of `St_n(C)`, with `C = C_2(𝔽₂)`.  For
`k ∈ K₂(n, C)`, the elements `cornerMap σ^m τ^m k` and `k` agree after two stabilizations.

The proof is induction on `∑ i, m i`.  To lower `m` by one at an index `ℓ`, conjugate once
stabilized by the corner element on the indices `ℓ`, `last n`
(`LVCornerShift.cornerConj_castSuccStab_cornerMap`, with `u = x₀`, `v = y₀`, `y₀ x₀ = 1`).
Twice stabilized, `K₂` is central (`LVCentral.castSuccStab_castSuccStab_mem_center`), so the
conjugation does nothing.  This generalizes `LVCornerShift.stab_stab_cornerMap_eq`, where the
potential is the indicator of an initial segment.
-/

namespace GroupApproximation.Full.LVCohnGraded

open SteinbergGroup

noncomputable section

/-- **Potential corner induction** (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii).
After two stabilizations, the potential corner map fixes every `k ∈ K₂(n, C_2(𝔽₂))`.  Stated for
all potentials of total weight `N`. -/
theorem skCohnGr_stab_stab_cornerMap_eq {n : ℕ}
    (k : SteinbergGroup (Fin n) LVCohnRelK1.CohnTwoF2) (hk : projection k = 1) :
    ∀ (N : ℕ) (m : Fin n → ℕ), ∑ i, m i = N →
      LVCentral.castSuccStab (n + 1) LVCohnRelK1.CohnTwoF2
          (LVCentral.castSuccStab n LVCohnRelK1.CohnTwoF2
            (LVCornerShift.cornerMap (skCohnGr_sigma m) (skCohnGr_tau m)
              (skCohnGr_tau_mul_sigma m) k)) =
        LVCentral.castSuccStab (n + 1) LVCohnRelK1.CohnTwoF2
          (LVCentral.castSuccStab n LVCohnRelK1.CohnTwoF2 k) := by
  intro N
  induction N with
  | zero =>
      intro m hm
      have h0 : ∀ i, m i = 0 := fun i => by
        have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
        omega
      rw [LVCornerShift.cornerMap_eq_self (skCohnGr_sigma m) (skCohnGr_tau m)
        (skCohnGr_tau_mul_sigma m) (fun i => by rw [skCohnGr_sigma, h0 i, pow_zero])
        (fun i => by rw [skCohnGr_tau, h0 i, pow_zero]) k]
  | succ N ih =>
      intro m hm
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, m ℓ ≠ 0 := by
        by_contra hcon
        push Not at hcon
        rw [Finset.sum_eq_zero (fun i _ => hcon i)] at hm
        omega
      have hsum : ∑ i, Function.update m ℓ (m ℓ - 1) i = N := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ ℓ)]
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ ℓ)] at hm
        omega
      have hσm : skCohnGr_sigma m ℓ =
          LVCohnRelK1.cx false * skCohnGr_sigma (Function.update m ℓ (m ℓ - 1)) ℓ := by
        simp only [skCohnGr_sigma]
        rw [Function.update_self, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m ℓ)]
      have hτm : skCohnGr_tau m ℓ =
          skCohnGr_tau (Function.update m ℓ (m ℓ - 1)) ℓ * LVCohnRelK1.cy false := by
        simp only [skCohnGr_tau]
        rw [Function.update_self, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m ℓ)]
      have hσo : ∀ j, j ≠ ℓ →
          skCohnGr_sigma m j = skCohnGr_sigma (Function.update m ℓ (m ℓ - 1)) j := by
        intro j hj
        simp only [skCohnGr_sigma]
        rw [Function.update_of_ne hj]
      have hτo : ∀ j, j ≠ ℓ →
          skCohnGr_tau m j = skCohnGr_tau (Function.update m ℓ (m ℓ - 1)) j := by
        intro j hj
        simp only [skCohnGr_tau]
        rw [Function.update_of_ne hj]
      have step := LVCornerShift.cornerConj_castSuccStab_cornerMap LVCohnRelK1.y0_x0 ℓ
        (skCohnGr_sigma (Function.update m ℓ (m ℓ - 1)))
        (skCohnGr_tau (Function.update m ℓ (m ℓ - 1))) (skCohnGr_sigma m) (skCohnGr_tau m)
        (skCohnGr_tau_mul_sigma _) (skCohnGr_tau_mul_sigma m) hσm hτm hσo hτo k
      have hc := LVCentral.castSuccStab_castSuccStab_mem_center (MonoidHom.mem_ker.mpr hk)
      rw [← step, map_mul, map_mul, map_inv, ih (Function.update m ℓ (m ℓ - 1)) hsum,
        Subgroup.mem_center_iff.mp hc, mul_inv_cancel_right]

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_stab_stab_cornerMap_eq

/-- **Potential corner maps act trivially on stable `K₂`**: padding by two indices identifies
`cornerMap σ^m τ^m k` with `k`, for `k ∈ K₂(n, C_2(𝔽₂))`.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem skCohnGr_indexMap_cornerMap_eq {n : ℕ} (m : Fin n → ℕ) (h : n ≤ n + 1 + 1)
    (k : SteinbergGroup (Fin n) LVCohnRelK1.CohnTwoF2) (hk : projection k = 1) :
    indexMap (Fin.castLEEmb h)
        (LVCornerShift.cornerMap (skCohnGr_sigma m) (skCohnGr_tau m)
          (skCohnGr_tau_mul_sigma m) k) =
      indexMap (Fin.castLEEmb h) k := by
  rw [LVCornerShift.indexMap_castLEEmb_eq_stab, LVCornerShift.indexMap_castLEEmb_eq_stab]
  exact skCohnGr_stab_stab_cornerMap_eq k hk _ m rfl

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_indexMap_cornerMap_eq

end

end GroupApproximation.Full.LVCohnGraded
