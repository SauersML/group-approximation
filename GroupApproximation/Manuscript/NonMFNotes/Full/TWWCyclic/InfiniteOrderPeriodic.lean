import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.InfiniteOrderCentral
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.Reduction

/-!
# Cyclic extension by an element some power of which centralizes the subgroup

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378), cyclic extension step, case in which `k` normalizes `H` and some
positive power `k ^ p` commutes with every element of `H`.

If some positive power of `k` lies in `H`, this is `isModelled_sup_zpowers_of_pow_mem`.
Otherwise `k ^ p` has infinite order modulo `H`, so the central case
(`isModelled_sup_zpowers_of_commute`) models `H' = H ⊔ ⟨k ^ p⟩`. The element `k`
normalizes `H'` and `k ^ p ∈ H'`, so the finite-order step models `H' ⊔ ⟨k⟩`, which
contains `H ⊔ ⟨k⟩` (`isModelled_sup_zpowers_of_pow_commute`). No amenability is used.
-/

namespace GroupApproximation.Full.TWWCyclic

variable {G : Type} [Group G]

theorem conj_mem_sup_zpowers_pow {H : Subgroup G} {k : G}
    (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) {p : ℕ} (hc : ∀ h ∈ H, k ^ p * h = h * k ^ p) :
    ∀ h ∈ H ⊔ Subgroup.zpowers (k ^ p), k * h * k⁻¹ ∈ H ⊔ Subgroup.zpowers (k ^ p) := by
  intro h hh
  obtain ⟨a, ha, n, rfl⟩ := exists_mul_zpow_of_commute hc hh
  have hX : Commute k⁻¹ ((k ^ p) ^ n) := ((Commute.self_pow k p).zpow_right n).inv_left
  have heq : k * (a * (k ^ p) ^ n) * k⁻¹ = k * a * k⁻¹ * (k ^ p) ^ n := by
    simp only [mul_assoc]
    rw [hX.eq]
  rw [heq]
  exact (H ⊔ Subgroup.zpowers (k ^ p)).mul_mem (Subgroup.mem_sup_left (hk a ha))
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers (k ^ p) n))

theorem conj_mem_sup_zpowers_pow' {H : Subgroup G} {k : G}
    (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) {p : ℕ} (hc : ∀ h ∈ H, k ^ p * h = h * k ^ p) :
    ∀ h ∈ H ⊔ Subgroup.zpowers (k ^ p), k⁻¹ * h * k ∈ H ⊔ Subgroup.zpowers (k ^ p) := by
  intro h hh
  obtain ⟨a, ha, n, rfl⟩ := exists_mul_zpow_of_commute hc hh
  have hX : Commute k ((k ^ p) ^ n) := (Commute.self_pow k p).zpow_right n
  have heq : k⁻¹ * (a * (k ^ p) ^ n) * k = k⁻¹ * a * k * (k ^ p) ^ n := by
    simp only [mul_assoc]
    rw [hX.eq]
  rw [heq]
  exact (H ⊔ Subgroup.zpowers (k ^ p)).mul_mem (Subgroup.mem_sup_left (hk' a ha))
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers (k ^ p) n))

/-- **Cyclic extension when a power of `k` centralizes `H`.** If `k` normalizes `H` and
`k ^ p` (`p > 0`) commutes with every element of `H`, then `IsModelled H` implies
`IsModelled (H ⊔ ⟨k⟩)` (`thm:fixed-radical-membership`, cyclic extension step; this covers
in particular every normalizing `k` whose conjugation action on `H` has finite order). -/
theorem isModelled_sup_zpowers_of_pow_commute {H : Subgroup G} {k : G}
    (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) {p : ℕ} (hp : 0 < p)
    (hc : ∀ h ∈ H, k ^ p * h = h * k ^ p) (hH : TWW.IsModelled H) :
    TWW.IsModelled (H ⊔ Subgroup.zpowers k) := by
  by_cases hfin : ∃ m : ℕ, 0 < m ∧ k ^ m ∈ H
  · obtain ⟨m, hm, hkm⟩ := hfin
    exact isModelled_sup_zpowers_of_pow_mem hk hk' hm hkm hH
  · have hinf : ∀ m : ℕ, 0 < m → (k ^ p) ^ m ∉ H := fun m hm hkm =>
      hfin ⟨p * m, Nat.mul_pos hp hm, by rw [pow_mul]; exact hkm⟩
    have hH' : TWW.IsModelled (H ⊔ Subgroup.zpowers (k ^ p)) :=
      isModelled_sup_zpowers_of_commute hc hinf hH
    have hkp : k ^ p ∈ H ⊔ Subgroup.zpowers (k ^ p) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (k ^ p))
    have h2 : TWW.IsModelled ((H ⊔ Subgroup.zpowers (k ^ p)) ⊔ Subgroup.zpowers k) :=
      isModelled_sup_zpowers_of_pow_mem (conj_mem_sup_zpowers_pow hk hc)
        (conj_mem_sup_zpowers_pow' hk' hc) hp hkp hH'
    exact isModelled_mono (sup_le_sup_right le_sup_left _) h2

end GroupApproximation.Full.TWWCyclic
