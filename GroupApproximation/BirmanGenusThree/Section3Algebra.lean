import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Torsion
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

/-!
# Chen–Salter, Section 3: the group-theoretic core of Lemma 3.3 and Corollary 3.4

Chen–Salter (arXiv:1804.11235v1, §3.1) study a homomorphism `s : H̄ → π₁(Σ_p)` on a finite-index
subgroup `H̄` that sends a power of each simple element to a power of the same element. Lemma 3.3
shows that the exponent is either always `0` or always the original exponent.

The argument uses only four properties of `π₁(Σ_p)` and of its set `S` of simple elements:
- the group is torsion-free;
- distinct powers of a nontrivial element are not conjugate (`PowConjRigid`);
- nontrivial commuting elements have a common nonzero power (`CommonPowers`);
- two simple elements with a common nonzero power are equal up to inversion, and `S` is closed under
  conjugation (`SimpleSystem`).

This file proves Lemma 3.3 and Corollary 3.4 for any group with these properties. For `π₁(Σ_2)` the
properties come from the surface-group library.
-/

namespace GroupApproximation.BirmanGenusThree.Section3

/-- Distinct powers of a nontrivial element are never conjugate. -/
def PowConjRigid (G : Type*) [Group G] : Prop :=
  ∀ γ : G, γ ≠ 1 → ∀ m n : ℤ, IsConj (γ ^ m) (γ ^ n) → m = n

/-- Two nontrivial commuting elements have a common nonzero power. -/
def CommonPowers (G : Type*) [Group G] : Prop :=
  ∀ x y : G, x ≠ 1 → y ≠ 1 → x * y = y * x → ∃ c d : ℤ, c ≠ 0 ∧ d ≠ 0 ∧ x ^ c = y ^ d

/-- The properties of the set `S` of simple elements that Lemma 3.3 uses. -/
structure SimpleSystem {G : Type*} [Group G] (S : Set G) : Prop where
  one_notMem : (1 : G) ∉ S
  conj_mem : ∀ α ∈ S, ∀ g : G, g * α * g⁻¹ ∈ S
  rootUnique : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → α ^ a = β ^ b → α = β ∨ α = β⁻¹
  exists_other : ∀ α ∈ S, ∃ β ∈ S, β ≠ α ∧ β ≠ α⁻¹

/-- The hypothesis of Chen–Salter's Lemma 3.3: `f` sends each power of a simple element that lies
in `H` to some power of the same element. -/
def PowerExponentForm {G : Type*} [Group G] (S : Set G) (H : Subgroup G) (f : H →* G) : Prop :=
  ∀ α ∈ S, ∀ (k : ℤ) (hk : α ^ k ∈ H), ∃ m : ℤ, f ⟨α ^ k, hk⟩ = α ^ m

variable {G : Type*} [Group G] [IsMulTorsionFree G] {S : Set G} {H : Subgroup G} {f : H →* G}

omit [IsMulTorsionFree G] in
/-- The conjugate `β^ℓ α^k β^{-ℓ}` as an element of `H`. -/
private lemma conj_pow_mem {α β : G} {k ℓ : ℤ} (hα : α ^ k ∈ H) (hβ : β ^ ℓ ∈ H) :
    (β ^ ℓ * α * (β ^ ℓ)⁻¹) ^ k ∈ H := by
  rw [conj_zpow]
  exact H.mul_mem (H.mul_mem hβ hα) (H.inv_mem hβ)

/-- The key step of Lemma 3.3. If `α, β` are simple and `β ≠ α^{±1}`, then either `f(α^k) = 1` or
`f(β^ℓ) = β^ℓ`. -/
theorem zero_or_id_of_ne (hG : PowConjRigid G) (hC : CommonPowers G) (hS : SimpleSystem S)
    (hf : PowerExponentForm S H f) {α β : G} (hαS : α ∈ S) (hβS : β ∈ S) (hne : β ≠ α)
    (hne' : β ≠ α⁻¹) {k ℓ : ℤ} (hα : α ^ k ∈ H) (hβ : β ^ ℓ ∈ H) :
    f ⟨α ^ k, hα⟩ = 1 ∨ f ⟨β ^ ℓ, hβ⟩ = β ^ ℓ := by
  have hα1 : α ≠ 1 := fun h => hS.one_notMem (h ▸ hαS)
  have hβ1 : β ≠ 1 := fun h => hS.one_notMem (h ▸ hβS)
  obtain ⟨mα, hmα⟩ := hf α hαS k hα
  obtain ⟨mβ, hmβ⟩ := hf β hβS ℓ hβ
  have hγS := hS.conj_mem α hαS (β ^ ℓ)
  obtain ⟨mγ, hmγ⟩ := hf _ hγS k (conj_pow_mem hα hβ)
  have hsplit : (⟨(β ^ ℓ * α * (β ^ ℓ)⁻¹) ^ k, conj_pow_mem hα hβ⟩ : H) =
      ⟨β ^ ℓ, hβ⟩ * ⟨α ^ k, hα⟩ * (⟨β ^ ℓ, hβ⟩ : H)⁻¹ := by
    ext; simp [conj_zpow]
  rw [hsplit, map_mul, map_mul, map_inv, hmα, hmβ, conj_zpow] at hmγ
  -- `hmγ : β^ℓ α^mγ β^{-ℓ} = β^mβ α^mα β^{-mβ}`, so `mγ = mα`.
  have hconj : IsConj (α ^ mγ) (α ^ mα) := by
    rw [isConj_iff]
    refine ⟨(β ^ mβ)⁻¹ * β ^ ℓ, ?_⟩
    calc (β ^ mβ)⁻¹ * β ^ ℓ * α ^ mγ * ((β ^ mβ)⁻¹ * β ^ ℓ)⁻¹
        = (β ^ mβ)⁻¹ * (β ^ ℓ * α ^ mγ * (β ^ ℓ)⁻¹) * β ^ mβ := by group
      _ = α ^ mα := by rw [← hmγ]; group
  have hγα : mγ = mα := hG α hα1 mγ mα hconj
  rw [hγα] at hmγ
  by_cases hmα0 : mα = 0
  · left; rw [hmα, hmα0, zpow_zero]
  by_cases hmβℓ : mβ = ℓ
  · right; rw [hmβ, hmβℓ]
  exfalso
  set x : G := β ^ (ℓ - mβ) with hx
  have hx1 : x ≠ 1 := by
    rw [hx, Ne, IsMulTorsionFree.zpow_eq_one_iff_right hβ1]
    exact fun h => hmβℓ (by omega)
  have ha1 : α ^ mα ≠ 1 := by
    rw [Ne, IsMulTorsionFree.zpow_eq_one_iff_right hα1]; exact hmα0
  have hcomm : x * α ^ mα = α ^ mα * x := by
    have hx' : x = (β ^ mβ)⁻¹ * β ^ ℓ := by
      rw [hx, ← zpow_neg, ← zpow_add, neg_add_eq_sub]
    rw [hx']
    calc (β ^ mβ)⁻¹ * β ^ ℓ * α ^ mα
        = (β ^ mβ)⁻¹ * (β ^ ℓ * α ^ mα * (β ^ ℓ)⁻¹) * β ^ ℓ := by group
      _ = α ^ mα * ((β ^ mβ)⁻¹ * β ^ ℓ) := by rw [← hmγ]; group
  obtain ⟨c, d, hc, hd, hcd⟩ := hC x (α ^ mα) hx1 ha1 hcomm
  rw [hx, ← zpow_mul, ← zpow_mul] at hcd
  have hℓ : ℓ - mβ ≠ 0 := fun h => hmβℓ (by omega)
  rcases hS.rootUnique β hβS α hαS _ _ (mul_ne_zero hℓ hc) (mul_ne_zero hmα0 hd) hcd with h | h
  · exact hne h
  · exact hne' h

end GroupApproximation.BirmanGenusThree.Section3
