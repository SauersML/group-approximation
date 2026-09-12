import GroupApproximation.GroupTheory.HigmanThompson.CompactCoreGerms
import GroupApproximation.Meta.AxiomGuard

/-!
# Proximality of `F_n` and `F_n'`

Hyde–Lodha, Lemma 3.3 (first half): "The standard actions of `F_n, F_n'` on `(0,1)` are proximal":
for every proper compact subset `U ⊂ (0, 1)` and nonempty open `V ⊂ (0, 1)` some element maps `U`
into `V`.  In the model on `ℚ` a compact subset of `(0, 1)` lies in some `[p, q] ⊂ (0, 1)` and a
nonempty open subset contains some `(u, v)`, so the statement is recorded with these intervals
(`IsProximalOnUnit`).

* `exists_commutator_compactCore_mapsTo`: `⁅core, core⁆` sends two points `a < b` of
  `ℤ[1/n] ∩ (0, 1)` to any two points `a' < b'` in the same residue classes: an element `k` of the core
  doing this, times a conjugate of `k⁻¹` supported beyond `b`.
* `isProximalOnUnit_commutator`: `F_n' = ⁅F_n, F_n⁆` is proximal; `isProximalOnUnit_compactF`: so is
  `F_n`.
-/

namespace GroupApproximation
namespace HigmanThompson

open scoped commutatorElement
open HydeLodha

/-- Proximality on `(0, 1)`, in the model on `ℚ`. -/
def IsProximalOnUnit (G : Subgroup (Equiv.Perm ℚ)) : Prop :=
  ∀ U : Set ℚ, (∃ p q : ℚ, 0 < p ∧ q < 1 ∧ U ⊆ Set.Icc p q) →
    ∀ u v : ℚ, 0 ≤ u → u < v → v ≤ 1 → ∃ f ∈ G, f '' U ⊆ Set.Ioo u v

variable {m : ℕ}

/-- **Two points in, two points out, by commutators.** -/
theorem exists_commutator_compactCore_mapsTo {a b a' b' : ℚ} (ha : ∃ M, a ∈ Grid (m + 2) M)
    (hb : ∃ M, b ∈ Grid (m + 2) M) (ha' : ∃ M, a' ∈ Grid (m + 2) M)
    (hb' : ∃ M, b' ∈ Grid (m + 2) M) (hra : ResEq m a' a) (hrb : ResEq m b' b)
    (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) (h0a' : 0 < a') (hab' : a' < b')
    (hb1' : b' < 1) :
    ∃ e ∈ ⁅compactCore m, compactCore m⁆, e a = a' ∧ e b = b' := by
  obtain ⟨k, hk, hka, hkb⟩ :=
    exists_compactCore_mapsTo ha hb ha' hb' hra hrb h0a hab hb1 h0a' hab' hb1'
  obtain ⟨c₀, d₀, hc₀, hd₀, h0c₀, hcd₀, hd₀1, hkW, -⟩ := compactCore_supportedIn₂ hk hk
  obtain ⟨c', hc'a, hc'b, hrc', hc'⟩ := exists_resEq_mem_Ioo (m := m) hc₀ hb1
  obtain ⟨d', hd'a, hd'b, hrd', hd'⟩ := exists_resEq_mem_Ioo (m := m) hd₀ hc'b
  obtain ⟨z, hz, hzc, hzd⟩ := exists_compactCore_mapsTo (m := m) hc₀ hd₀ hc' hd' hrc' hrd'
    h0c₀ hcd₀ hd₀1 (by linarith) hd'a hd'b
  refine ⟨⁅k, z⁆, Subgroup.commutator_mem_commutator hk hz, ?_, ?_⟩
  · have hzx : z⁻¹ a ∉ Set.Ioo c₀ d₀ := by
      intro hmem
      have h := image_Ioo_subset (compactF_strictMono (compactCore_le hz)) c₀ d₀
        ⟨z⁻¹ a, hmem, Equiv.apply_symm_apply z a⟩
      rw [hzc, hzd] at h
      linarith [h.1]
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    rw [hkW.inv _ hzx, perm_apply_inv_self z a, hka]
  · have hzx : z⁻¹ b ∉ Set.Ioo c₀ d₀ := by
      intro hmem
      have h := image_Ioo_subset (compactF_strictMono (compactCore_le hz)) c₀ d₀
        ⟨z⁻¹ b, hmem, Equiv.apply_symm_apply z b⟩
      rw [hzc, hzd] at h
      linarith [h.1]
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    rw [hkW.inv _ hzx, perm_apply_inv_self z b, hkb]

variable (m)

/-- **`F_n'` is proximal on `(0, 1)`** (Hyde–Lodha, Lemma 3.3). -/
theorem isProximalOnUnit_commutator : IsProximalOnUnit ⁅compactF m 1, compactF m 1⁆ := by
  rw [commutator_compactF_eq m]
  rintro U ⟨p, q, hp, hq, hU⟩ u v hu huv hv
  rcases Set.eq_empty_or_nonempty U with hUe | ⟨x₀, hx₀⟩
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [hUe, Set.image_empty]
    exact Set.empty_subset _
  have hpq : p ≤ q := le_trans (hU hx₀).1 (hU hx₀).2
  obtain ⟨p₀, hp₀1, hp₀2, hp₀⟩ := exists_grid_mem_Ioo (m := m) hp
  obtain ⟨q₀, hq₀1, hq₀2, hq₀⟩ := exists_grid_mem_Ioo (m := m) hq
  have hq₀q : q < q₀ := hq₀1
  have hpq₀ : p₀ < q₀ := by linarith
  obtain ⟨p', hp'1, hp'2, hrp', hp'⟩ :=
    exists_resEq_mem_Ioo (m := m) hp₀ (show u < (u + v) / 2 by linarith)
  obtain ⟨q', hq'1, hq'2, hrq', hq'⟩ := exists_resEq_mem_Ioo (m := m) hq₀ (show p' < v by linarith)
  obtain ⟨e, he, hep, heq⟩ := exists_commutator_compactCore_mapsTo hp₀ hq₀ hp' hq' hrp' hrq'
    hp₀1 hpq₀ hq₀2 (by linarith) hq'1 (by linarith)
  have hmono := compactF_strictMono (compactCore_le (commutator_le_self _ he))
  refine ⟨e, he, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hU hx
  have h1 : e p₀ < e x := hmono (lt_of_lt_of_le hp₀2 hx'.1)
  have h2 : e x < e q₀ := hmono (lt_of_le_of_lt hx'.2 hq₀q)
  rw [hep] at h1
  rw [heq] at h2
  exact ⟨by linarith, by linarith⟩

/-- **`F_n` is proximal on `(0, 1)`.** -/
theorem isProximalOnUnit_compactF : IsProximalOnUnit (compactF m 1) := by
  intro U hU u v hu huv hv
  obtain ⟨f, hf, hfU⟩ := isProximalOnUnit_commutator m U hU u v hu huv hv
  exact ⟨f, commutator_le_self _ hf, hfU⟩

#audit_axioms GroupApproximation.HigmanThompson.isProximalOnUnit_commutator
#audit_axioms GroupApproximation.HigmanThompson.isProximalOnUnit_compactF

end HigmanThompson
end GroupApproximation
