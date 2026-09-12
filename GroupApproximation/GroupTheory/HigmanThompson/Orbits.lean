import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Pi
import GroupApproximation.GroupTheory.HigmanThompson.Proximal
import GroupApproximation.Meta.AxiomGuard

/-!
# Orbits of `F_n` on tuples

Hyde–Lodha, Proposition 3.5: "For each `k ≥ 1`, we consider two linearly ordered `k`-tuples
`(x_1,...,x_k)` and `(y_1,...,y_k)` in `ℤ[1/n] ∩ (0,1)`.  Then the following are equivalent:
(1) there is an element `f ∈ F_n` such that `x_i·f = y_i` for each `i`; (2) there is an element
`f ∈ F_n'` such that `x_i·f = y_i` for each `i`; (3) `θ_n(x_i) = θ_n(y_i)` for each `i`.  It follows that
for every `k`, `F_n'` has finitely many orbits on `(ℤ[1/n] ∩ (0,1))^k`."

`θ_n(x) = θ_n(y)` is recorded as `ResEq m x y`, `x - y ∈ (n-1) ℤ[1/n]`, `n = m + 2` (for `x = k/n^l`,
`y = k'/n^l` this is `k ≡ k' mod n - 1`).

* `exists_compactCore_tuple`: condition (3) gives an element of the compactly supported core, by
  induction on `k`: map the last `k - 1` points, then move the first below the second.
* `exists_commutator_compactCore_tuple`: and an element of `⁅core, core⁆ = F_n'`.
* `orbits_tfae_one_three`, `orbits_tfae_two_three`: the equivalences.
* `exists_resEq_unit`: every point of `ℤ[1/n]` has the residue of some `j/n`, `1 ≤ j ≤ n - 1`
  (Lemma 3.6).
* `finite_orbits`: finitely many `F_n'`-orbits on increasing `k`-tuples.
-/

namespace GroupApproximation
namespace HigmanThompson

open scoped commutatorElement
open HydeLodha

variable {m : ℕ}

/-- Increasing tuples of points of `ℤ[1/n] ∩ (0, 1)`. -/
def IsUnitTuple (m : ℕ) {k : ℕ} (x : Fin k → ℚ) : Prop :=
  StrictMono x ∧ (∀ i, ∃ M, x i ∈ Grid (m + 2) M) ∧ (∀ i, 0 < x i) ∧ ∀ i, x i < 1

theorem IsUnitTuple.tail {k : ℕ} {x : Fin (k + 1) → ℚ} (hx : IsUnitTuple m x) :
    IsUnitTuple m (fun i : Fin k => x i.succ) :=
  ⟨hx.1.comp Fin.strictMono_succ, fun i => hx.2.1 i.succ, fun i => hx.2.2.1 i.succ,
    fun i => hx.2.2.2 i.succ⟩

/-- **Condition (3) gives an element of the core.** -/
theorem exists_compactCore_tuple (k : ℕ) :
    ∀ x y : Fin k → ℚ, IsUnitTuple m x → IsUnitTuple m y → (∀ i, ResEq m (y i) (x i)) →
      ∃ f ∈ compactCore m, ∀ i, f (x i) = y i := by
  induction k with
  | zero => exact fun x y _ _ _ => ⟨1, (compactCore m).one_mem, fun i => i.elim0⟩
  | succ k ih =>
    intro x y hx hy hres
    rcases k with _ | k
    · obtain ⟨α, hα1, hα2, hα⟩ := exists_grid_mem_Ioo (m := m) (lt_min (hx.2.2.1 0) (hy.2.2.1 0))
      obtain ⟨β, hβ1, hβ2, hβ⟩ := exists_grid_mem_Ioo (m := m) (max_lt (hx.2.2.2 0) (hy.2.2.2 0))
      have hm1 := min_le_left (x 0) (y 0)
      have hm2 := min_le_right (x 0) (y 0)
      have hM1 := le_max_left (x 0) (y 0)
      have hM2 := le_max_right (x 0) (y 0)
      obtain ⟨h, hh, hlow, hhigh, hxy⟩ := exists_move m hα hβ (hres 0).symm (by linarith)
        (by linarith) (by linarith) (by linarith)
      refine ⟨h, move_mem_compactCore hh hα1 hβ2 hlow hhigh, fun i => ?_⟩
      rw [Fin.fin_one_eq_zero i]
      exact hxy
    · obtain ⟨f₁, hf₁, hf₁x₀⟩ := ih (fun i => x i.succ) (fun i => y i.succ) hx.tail hy.tail
        (fun i => hres i.succ)
      have hf₁x : ∀ i : Fin (k + 1), f₁ (x i.succ) = y i.succ := hf₁x₀
      have hF₁ := compactCore_le hf₁
      have hmono := compactF_strictMono hF₁
      have hp0 : 0 < f₁ (x 0) := by
        have h := hmono (hx.2.2.1 0)
        rwa [compactF_fix_nonpos hF₁ le_rfl] at h
      have hp1 : f₁ (x 0) < y (Fin.succ 0) := by
        have h := hmono (hx.1 (Fin.succ_pos (0 : Fin (k + 1))))
        rwa [hf₁x 0] at h
      obtain ⟨M₀, hM₀⟩ := hx.2.1 0
      have hres₀ : ResEq m (f₁ (x 0)) (y 0) :=
        (resEq_apply_of_fix hF₁.1 (fun t ht => compactF_fix_nonpos hF₁ ht) hM₀).trans (hres 0).symm
      obtain ⟨α, hα1, hα2, hα⟩ := exists_grid_mem_Ioo (m := m) (lt_min hp0 (hy.2.2.1 0))
      have hm1 := min_le_left (f₁ (x 0)) (y 0)
      have hm2 := min_le_right (f₁ (x 0)) (y 0)
      have hy01 : y 0 < y (Fin.succ 0) := hy.1 (Fin.succ_pos (0 : Fin (k + 1)))
      obtain ⟨f₂, hf₂, hlow, hhigh, hf₂x⟩ := exists_move m hα (hy.2.1 (Fin.succ 0)) hres₀
        (by linarith) (by linarith) hp1 hy01
      refine ⟨f₂ * f₁, (compactCore m).mul_mem
        (move_mem_compactCore hf₂ hα1 (hy.2.2.2 (Fin.succ 0)) hlow hhigh) hf₁, fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Equiv.Perm.mul_apply, hf₂x]
      · rw [Equiv.Perm.mul_apply, hf₁x j]
        refine hhigh _ (hy.1.monotone ?_)
        exact Fin.succ_le_succ_iff.mpr (Fin.zero_le j)

/-- **Condition (3) gives an element of `F_n' = ⁅core, core⁆`.** -/
theorem exists_commutator_compactCore_tuple (k : ℕ) (x y : Fin k → ℚ) (hx : IsUnitTuple m x)
    (hy : IsUnitTuple m y) (hres : ∀ i, ResEq m (y i) (x i)) :
    ∃ e ∈ ⁅compactCore m, compactCore m⁆, ∀ i, e (x i) = y i := by
  rcases k with _ | k
  · exact ⟨1, Subgroup.one_mem _, fun i => i.elim0⟩
  obtain ⟨f, hf, hfx⟩ := exists_compactCore_tuple (k + 1) x y hx hy hres
  obtain ⟨c₀, d₀, hc₀, hd₀, h0c₀, hcd₀, hd₀1, hfW, -⟩ := compactCore_supportedIn₂ hf hf
  obtain ⟨c', hc'a, hc'b, hrc', hc'⟩ := exists_resEq_mem_Ioo (m := m) hc₀ (hx.2.2.2 (Fin.last k))
  obtain ⟨d', hd'a, hd'b, hrd', hd'⟩ := exists_resEq_mem_Ioo (m := m) hd₀ hc'b
  obtain ⟨z, hz, hzc, hzd⟩ := exists_compactCore_mapsTo (m := m) hc₀ hd₀ hc' hd' hrc' hrd'
    h0c₀ hcd₀ hd₀1 (by linarith [hx.2.2.1 (Fin.last k)]) hd'a hd'b
  refine ⟨⁅f, z⁆, Subgroup.commutator_mem_commutator hf hz, fun i => ?_⟩
  have hxi : x i ≤ x (Fin.last k) := hx.1.monotone (Fin.le_last i)
  have hzx : z⁻¹ (x i) ∉ Set.Ioo c₀ d₀ := by
    intro hmem
    have h := image_Ioo_subset (compactF_strictMono (compactCore_le hz)) c₀ d₀
      ⟨z⁻¹ (x i), hmem, Equiv.apply_symm_apply z (x i)⟩
    rw [hzc, hzd] at h
    linarith [h.1]
  rw [commutatorElement_def]
  simp only [Equiv.Perm.mul_apply]
  rw [hfW.inv _ hzx, perm_apply_inv_self z (x i), hfx i]

theorem resEq_of_compactF_tuple {k : ℕ} {x y : Fin k → ℚ} (hx : IsUnitTuple m x) {f : Equiv.Perm ℚ}
    (hf : f ∈ compactF m 1) (hfx : ∀ i, f (x i) = y i) (i : Fin k) : ResEq m (y i) (x i) := by
  obtain ⟨M, hM⟩ := hx.2.1 i
  rw [← hfx i]
  exact resEq_apply_of_fix hf.1 (fun t ht => compactF_fix_nonpos hf ht) hM

variable (m)

/-- **Proposition 3.5, (1) ⇔ (3).** -/
theorem orbits_tfae_one_three {k : ℕ} (x y : Fin k → ℚ) (hx : IsUnitTuple m x)
    (hy : IsUnitTuple m y) :
    (∃ f ∈ compactF m 1, ∀ i, f (x i) = y i) ↔ ∀ i, ResEq m (y i) (x i) := by
  constructor
  · rintro ⟨f, hf, hfx⟩
    exact resEq_of_compactF_tuple hx hf hfx
  · intro hres
    obtain ⟨f, hf, hfx⟩ := exists_compactCore_tuple k x y hx hy hres
    exact ⟨f, compactCore_le hf, hfx⟩

/-- **Proposition 3.5, (2) ⇔ (3).** -/
theorem orbits_tfae_two_three {k : ℕ} (x y : Fin k → ℚ) (hx : IsUnitTuple m x)
    (hy : IsUnitTuple m y) :
    (∃ f ∈ ⁅compactF m 1, compactF m 1⁆, ∀ i, f (x i) = y i) ↔ ∀ i, ResEq m (y i) (x i) := by
  rw [commutator_compactF_eq m]
  constructor
  · rintro ⟨f, hf, hfx⟩
    exact resEq_of_compactF_tuple hx (compactCore_le (commutator_le_self _ hf)) hfx
  · exact exists_commutator_compactCore_tuple k x y hx hy

/-- **Lemma 3.6, residues.**  Every point of `ℤ[1/n]` has the residue of some `j/n`, `1 ≤ j ≤ n - 1`. -/
theorem exists_resEq_unit {x : ℚ} (hx : ∃ M, x ∈ Grid (m + 2) M) :
    ∃ j : Fin (m + 1), ResEq m x (((j : ℕ) + 1 : ℚ) / ((m : ℚ) + 2)) := by
  obtain ⟨M, e, he⟩ := hx
  have hcast : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  rw [hcast] at he
  have hm1 : (0 : ℤ) < (m : ℤ) + 1 := by omega
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = ((e - 1) % ((m : ℤ) + 1)).toNat := ⟨_, rfl⟩
  have hj0 : 0 ≤ (e - 1) % ((m : ℤ) + 1) := Int.emod_nonneg _ hm1.ne'
  have hjlt : (e - 1) % ((m : ℤ) + 1) < (m : ℤ) + 1 := Int.emod_lt_of_pos _ hm1
  have hjZ : (j : ℤ) = (e - 1) % ((m : ℤ) + 1) := by
    rw [hjdef]
    exact Int.toNat_of_nonneg hj0
  have hjm : j < m + 1 := by omega
  obtain ⟨q, hq⟩ : ∃ q : ℤ, e - 1 = ((m : ℤ) + 1) * q + j := by
    refine ⟨(e - 1) / ((m : ℤ) + 1), ?_⟩
    rw [hjZ]
    exact (Int.mul_ediv_add_emod _ _).symm
  obtain ⟨c, hc⟩ := mTwo_pow_sub_one_dvd (m := m) M
  have hcQ : ((m : ℚ) + 2) ^ M - 1 = ((m : ℚ) + 1) * c := by exact_mod_cast hc
  refine ⟨⟨j, hjm⟩, M + 1, q * ((m : ℤ) + 2) + (j + 1) - (j + 1) * c, ?_⟩
  have hqQ : (e : ℚ) - 1 = ((m : ℚ) + 1) * q + j := by exact_mod_cast hq
  have hn : ((m : ℚ) + 2) ≠ 0 := mTwo_pos.ne'
  have hdiv : ((j : ℚ) + 1) / ((m : ℚ) + 2) * ((m : ℚ) + 2) ^ (M + 1) =
      ((j : ℚ) + 1) * ((m : ℚ) + 2) ^ M := by
    calc ((j : ℚ) + 1) / ((m : ℚ) + 2) * ((m : ℚ) + 2) ^ (M + 1)
        = (((j : ℚ) + 1) / ((m : ℚ) + 2) * ((m : ℚ) + 2)) * ((m : ℚ) + 2) ^ M := by
          rw [pow_succ]
          ring
      _ = ((j : ℚ) + 1) * ((m : ℚ) + 2) ^ M := by rw [div_mul_cancel₀ _ hn]
  rw [sub_mul, hdiv, pow_succ, ← mul_assoc, he]
  push_cast
  linear_combination ((m : ℚ) + 2) * hqQ - ((j : ℚ) + 1) * hcQ

/-- **Finitely many `F_n'`-orbits on increasing tuples.** -/
theorem finite_orbits (k : ℕ) :
    ∃ T : Finset (Fin k → ℚ), ∀ x : Fin k → ℚ, IsUnitTuple m x →
      ∃ t ∈ T, ∃ f ∈ ⁅compactF m 1, compactF m 1⁆, ∀ i, f (t i) = x i := by
  classical
  let pat : (Fin k → ℚ) → (Fin k → Fin (m + 1)) := fun x i =>
    if h : ∃ M, x i ∈ Grid (m + 2) M then Classical.choose (exists_resEq_unit m h) else 0
  have hpat : ∀ x : Fin k → ℚ, IsUnitTuple m x → ∀ i,
      ResEq m (x i) ((((pat x i : Fin (m + 1)) : ℕ) + 1 : ℚ) / ((m : ℚ) + 2)) := by
    intro x hx i
    have h := hx.2.1 i
    simp only [pat, dif_pos h]
    exact Classical.choose_spec (exists_resEq_unit m h)
  let rep : (Fin k → Fin (m + 1)) → (Fin k → ℚ) := fun r =>
    if h : ∃ x, IsUnitTuple m x ∧ pat x = r then Classical.choose h else 0
  refine ⟨Finset.univ.image rep, fun x hx => ⟨rep (pat x), Finset.mem_image_of_mem _
    (Finset.mem_univ _), ?_⟩⟩
  have hex : ∃ x', IsUnitTuple m x' ∧ pat x' = pat x := ⟨x, hx, rfl⟩
  have hrep : IsUnitTuple m (rep (pat x)) ∧ pat (rep (pat x)) = pat x := by
    simp only [rep, dif_pos hex]
    exact Classical.choose_spec hex
  refine (orbits_tfae_two_three m (rep (pat x)) x hrep.1 hx).mpr fun i => ?_
  have h1 := hpat x hx i
  have h2 := hpat (rep (pat x)) hrep.1 i
  rw [hrep.2] at h2
  exact h1.trans h2.symm

#audit_axioms GroupApproximation.HigmanThompson.orbits_tfae_one_three
#audit_axioms GroupApproximation.HigmanThompson.orbits_tfae_two_three
#audit_axioms GroupApproximation.HigmanThompson.finite_orbits

end HigmanThompson
end GroupApproximation
