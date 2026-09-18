import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPPTorus
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroSLFourFPComm
import GroupApproximation.Meta.AxiomGuard

/-!
# The Steinberg relations in `P m`, and `ψ : St_4(ℤ[1/m]) → P m` (bh-met-91m)

The Steinberg relations among the `czStFourFP_XP m α` hold for integer coefficients (they come
from `St_4(ℤ)`).  For general coefficients `a, b` conjugate by a large power of a torus letter
`T s` that scales both roots by positive powers of `m` (`T_{il}` for the pair `(ij, kl)`, `T_{ik}`
for the pair `(ij, jk)`): this makes the coefficients integral, and conjugation is injective.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement

/-- **Commutation transfer.**  If conjugation by `g` scales both families and the relation holds
for integers, it holds whenever some `g ^ N` makes both coefficients integral. -/
theorem czStFourFP_comm_transfer {G R : Type*} [Group G] [CommRing R] {g : G}
    {Xa Xb : R → G} {ca cb : R} (ha : ∀ r, g * Xa r * g⁻¹ = Xa (ca * r))
    (hb : ∀ r, g * Xb r * g⁻¹ = Xb (cb * r))
    (hint : ∀ n₁ n₂ : ℤ, Commute (Xa n₁) (Xb n₂)) {a b : R}
    (hN : ∃ N : ℕ, ∃ n₁ n₂ : ℤ, ca ^ N * a = n₁ ∧ cb ^ N * b = n₂) :
    Commute (Xa a) (Xb b) := by
  obtain ⟨N, n₁, n₂, h₁, h₂⟩ := hN
  rw [← Commute.conj_iff (g ^ N), czStFourFP_conj_pow_iter ha N a,
    czStFourFP_conj_pow_iter hb N b, h₁, h₂]
  exact hint n₁ n₂

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_comm_transfer

/-- **Commutator transfer.** -/
theorem czStFourFP_adj_transfer {G R : Type*} [Group G] [CommRing R] {g : G}
    {Xa Xb Xc : R → G} {ca cb : R} (ha : ∀ r, g * Xa r * g⁻¹ = Xa (ca * r))
    (hb : ∀ r, g * Xb r * g⁻¹ = Xb (cb * r)) (hc : ∀ r, g * Xc r * g⁻¹ = Xc (ca * cb * r))
    (hint : ∀ n₁ n₂ : ℤ, ⁅Xa n₁, Xb n₂⁆ = Xc ((n₁ : R) * n₂)) {a b : R}
    (hN : ∃ N : ℕ, ∃ n₁ n₂ : ℤ, ca ^ N * a = n₁ ∧ cb ^ N * b = n₂) :
    ⁅Xa a, Xb b⁆ = Xc (a * b) := by
  obtain ⟨N, n₁, n₂, h₁, h₂⟩ := hN
  have e := hint n₁ n₂
  rw [← h₁, ← h₂, ← czStFourFP_conj_pow_iter ha N a, ← czStFourFP_conj_pow_iter hb N b,
    ← czStFourFP_conj_commutator,
    show ca ^ N * a * (cb ^ N * b) = (ca * cb) ^ N * (a * b) by ring,
    ← czStFourFP_conj_pow_iter hc N (a * b)] at e
  exact mul_left_cancel (mul_right_cancel e)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_adj_transfer

/-- Eventually integral: `m ^ (N + d) r ∈ ℤ` for all `d`. -/
theorem czStFourFP_evInt (m : ℕ) (r : czStFourFP_R m) :
    ∃ N : ℕ, ∀ d : ℕ, ∃ n : ℤ,
      ((m : ℤ) : czStFourFP_R m) ^ (N + d) * r = (n : czStFourFP_R m) := by
  obtain ⟨k, n, h⟩ := czStFourFP_surj m r
  refine ⟨2 * k, fun d => ⟨(m : ℤ) ^ d * n, ?_⟩⟩
  rw [Int.cast_mul, Int.cast_pow, ← h]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_evInt

/-- A common level making two coefficients integral. -/
theorem czStFourFP_hN (m : ℕ) {e₁ e₂ : ℕ} (h₁ : 0 < e₁) (h₂ : 0 < e₂)
    (a b : czStFourFP_R m) :
    ∃ N : ℕ, ∃ n₁ n₂ : ℤ, (((m : ℤ) : czStFourFP_R m) ^ e₁) ^ N * a = n₁ ∧
      (((m : ℤ) : czStFourFP_R m) ^ e₂) ^ N * b = n₂ := by
  obtain ⟨Na, ha⟩ := czStFourFP_evInt m a
  obtain ⟨Nb, hb⟩ := czStFourFP_evInt m b
  obtain ⟨d₁, hd₁⟩ := Nat.exists_eq_add_of_le
    ((Nat.le_add_right Na Nb).trans (Nat.le_mul_of_pos_left (Na + Nb) h₁))
  obtain ⟨d₂, hd₂⟩ := Nat.exists_eq_add_of_le
    ((Nat.le_add_left Nb Na).trans (Nat.le_mul_of_pos_left (Na + Nb) h₂))
  obtain ⟨n₁, hn₁⟩ := ha d₁
  obtain ⟨n₂, hn₂⟩ := hb d₂
  exact ⟨Na + Nb, n₁, n₂, by rw [← pow_mul, hd₁, hn₁], by rw [← pow_mul, hd₂, hn₂]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_hN

section Positivity

variable {I : Type*} [DecidableEq I] {a b i j : I}

theorem czStFourFP_chi_pos_left (hab : a ≠ b) (hja : j ≠ a) : 0 < czStFourFP_chi a b a j := by
  rw [czStFourFP_chi, if_pos rfl, if_neg hab, if_neg hja]
  split_ifs <;> norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_pos_left

theorem czStFourFP_chi_pos_right (hib : i ≠ b) (hab : a ≠ b) : 0 < czStFourFP_chi a b i b := by
  rw [czStFourFP_chi, if_neg hib, if_neg hab.symm, if_pos rfl]
  split_ifs <;> norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_pos_right

end Positivity

/-- The commutation relation in `P m`: conjugate by `T_{il}`. -/
theorem czStFourFP_P_commute (m : ℕ) (hm : 0 < m) (i j k l : Fin 4) (hij : i ≠ j)
    (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : czStFourFP_R m) :
    Commute (czStFourFP_XP m ⟨(i, j), hij⟩ a) (czStFourFP_XP m ⟨(k, l), hkl⟩ b) := by
  have p₁ := czStFourFP_chi_pos_left hli.symm hij.symm
  have p₂ := czStFourFP_chi_pos_right hkl hli.symm
  have hN := czStFourFP_hN m (e₁ := (czStFourFP_chi i l i j).toNat)
    (e₂ := (czStFourFP_chi i l k l).toNat) (by omega) (by omega) a b
  refine czStFourFP_comm_transfer (Xa := czStFourFP_XP m ⟨(i, j), hij⟩)
    (Xb := czStFourFP_XP m ⟨(k, l), hkl⟩)
    (czStFourFP_XP_conj_T m hm ⟨(i, l), hli.symm⟩ ⟨(i, j), hij⟩ p₁.le)
    (czStFourFP_XP_conj_T m hm ⟨(i, l), hli.symm⟩ ⟨(k, l), hkl⟩ p₂.le) (fun n₁ n₂ => ?_) hN
  rw [czStFourFP_XP_int m hm, czStFourFP_XP_int m hm]
  exact (czStFourFP_Y_commute m i j k l hij hkl hjk hli).zpow_zpow n₁ n₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_P_commute

/-- The commutator relation in `P m`: conjugate by `T_{ik}`. -/
theorem czStFourFP_P_adj (m : ℕ) (hm : 0 < m) (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : czStFourFP_R m) :
    ⁅czStFourFP_XP m ⟨(i, j), hij⟩ a, czStFourFP_XP m ⟨(j, k), hjk⟩ b⁆ =
      czStFourFP_XP m ⟨(i, k), hik⟩ (a * b) := by
  have hc : ∀ r, czStFourFP_T m ⟨(i, k), hik⟩ * czStFourFP_XP m ⟨(i, k), hik⟩ r *
      (czStFourFP_T m ⟨(i, k), hik⟩)⁻¹ = czStFourFP_XP m ⟨(i, k), hik⟩
        (((m : ℤ) : czStFourFP_R m) * ((m : ℤ) : czStFourFP_R m) * r) := fun r => by
    rw [czStFourFP_XP_conj_t m hm _ r, sq]
  obtain ⟨N, n₁, n₂, h₁, h₂⟩ := czStFourFP_hN m Nat.one_pos Nat.one_pos a b
  rw [pow_one] at h₁ h₂
  refine czStFourFP_adj_transfer (Xa := czStFourFP_XP m ⟨(i, j), hij⟩)
    (Xb := czStFourFP_XP m ⟨(j, k), hjk⟩) (Xc := czStFourFP_XP m ⟨(i, k), hik⟩)
    (czStFourFP_XP_conj_T_one m hm ⟨(i, k), hik⟩ ⟨(i, j), hij⟩
      (czStFourFP_chi_ak hik hij.symm hjk))
    (czStFourFP_XP_conj_T_one m hm ⟨(i, k), hik⟩ ⟨(j, k), hjk⟩
      (czStFourFP_chi_kb hik hij.symm hjk)) hc (fun n₁ n₂ => ?_) ⟨N, n₁, n₂, h₁, h₂⟩
  rw [czStFourFP_XP_int m hm, czStFourFP_XP_int m hm, ← Int.cast_mul, czStFourFP_XP_int m hm]
  exact czSLFourFP_commutator_zpow_zpow (czStFourFP_Y_commutator m i j k hij hjk hik)
    (czStFourFP_Y_commute m i j i k hij hik hij.symm hik.symm)
    (czStFourFP_Y_commute m j k i k hjk hik hik.symm hjk.symm) n₁ n₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_P_adj

/-- The generator map `x_ij(r) ↦ XP_{ij}(r)`. -/
noncomputable def czStFourFP_psiGen (m : ℕ) (g : SteinbergGenerator (Fin 4) (czStFourFP_R m)) :
    czStFourFP_P m :=
  czStFourFP_XP m ⟨(g.row, g.column), g.row_ne_column⟩ g.coefficient

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_psiGen

theorem czStFourFP_psi_rels (m : ℕ) (hm : 0 < m) :
    ∀ w ∈ SteinbergGroup.relations (I := Fin 4) (R := czStFourFP_R m),
      FreeGroup.lift (czStFourFP_psiGen m) w = 1 := by
  intro w hw
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      change czStFourFP_XP m ⟨(i, j), hij⟩ a * czStFourFP_XP m ⟨(i, j), hij⟩ b *
        (czStFourFP_XP m ⟨(i, j), hij⟩ (a + b))⁻¹ = 1
      rw [← czStFourFP_XP_add m hm, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅czStFourFP_XP m ⟨(i, j), hij⟩ a, czStFourFP_XP m ⟨(k, l), hkl⟩ b⁆ = 1
      exact (czStFourFP_P_commute m hm i j k l hij hkl hjk hli a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅czStFourFP_XP m ⟨(i, j), hij⟩ a, czStFourFP_XP m ⟨(j, k), hjk⟩ b⁆ *
        (czStFourFP_XP m ⟨(i, k), hik⟩ (a * b))⁻¹ = 1
      rw [czStFourFP_P_adj m hm i j k hij hjk hik a b, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_psi_rels

/-- **The section** `ψ : St_4(ℤ[1/m]) → P m`. -/
noncomputable def czStFourFP_psi (m : ℕ) (hm : 0 < m) :
    SteinbergGroup (Fin 4) (czStFourFP_R m) →* czStFourFP_P m :=
  PresentedGroup.toGroup (czStFourFP_psi_rels m hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_psi

theorem czStFourFP_psi_x (m : ℕ) (hm : 0 < m) (i j : Fin 4) (hij : i ≠ j)
    (r : czStFourFP_R m) :
    czStFourFP_psi m hm (SteinbergGroup.x i j hij r) = czStFourFP_XP m ⟨(i, j), hij⟩ r :=
  PresentedGroup.toGroup.of (czStFourFP_psi_rels m hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_psi_x

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
