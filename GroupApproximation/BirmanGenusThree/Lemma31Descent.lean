import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.Index

/-!
# Lemma 3.1, algebraic core: a homomorphism that kills the center descends to the quotient

In Chen–Salter's Section 3 (arXiv:1804.11235v1, §3.1), as used in genus 3
(research/artifacts/bh-birman-genus3-section-2026-09-12.md §3, items 2–3), the map `s̃ = p_{1,∗} ∘ σ` is defined on
`H = π₁(UT Σ₂) ∩ L`. Lemma C gives `σ(T_c^k) = T_{c̃}^k`, and capping `c̃` kills that twist, so `s̃` kills the center
`H ∩ ⟨T_c⟩`. Lemma 3.1 says that `s̃` then factors through the image `H̄ ≤ π₁(Σ₂)`.

This file proves the factorization for any homomorphism `ϖ : E →* Q` and subgroup `H ≤ E`, together with the step
that turns Lemma 3.2's formula on lifts into the hypothesis of Lemma 3.3 on `H̄`.

* `descend`: if `f : H →* G` kills `H ∩ ker ϖ`, it factors through `H.map ϖ` (`descend_apply`, `descend_unique`).
* `lemma_3_1_descent`: if `ϖ` is onto with kernel `⟨z⟩`, `H` has finite index and `f` kills the powers of `z` in `H`,
  then `H.map ϖ` has finite index and the factorization exists and is unique.
* `descend_zpow_form`: suppose every `α ∈ S` has a lift `α'` on whose powers in `H` the map `f` takes values in `⟨α⟩`,
  and roots of powers of elements of `S` are powers. Then the descended map sends each `α ^ k ∈ H.map ϖ` into `⟨α⟩`,
  which is the hypothesis of Lemma 3.3.
-/

namespace GroupApproximation.BirmanGenusThree

variable {E Q G : Type*} [Group E] [Group Q] [Group G] (ϖ : E →* Q) {H : Subgroup E}

/-- A chosen preimage in `H` of an element of `H.map ϖ`. -/
noncomputable def mapPreimage (q : H.map ϖ) : H :=
  ⟨(Subgroup.mem_map.mp q.2).choose, (Subgroup.mem_map.mp q.2).choose_spec.1⟩

theorem map_mapPreimage (q : H.map ϖ) : ϖ (mapPreimage ϖ q) = q :=
  (Subgroup.mem_map.mp q.2).choose_spec.2

/-- If `f` kills `H ∩ ker ϖ`, then `f` is constant on the fibers of `ϖ` in `H`. -/
theorem descend_eq_of_map_eq (f : H →* G) (hf : ∀ h : H, ϖ h = 1 → f h = 1) {h h' : H}
    (hh : ϖ h = ϖ h') : f h = f h' := by
  have h1 : f (h⁻¹ * h') = 1 := hf _ (by simp [hh])
  rwa [map_mul, map_inv, inv_mul_eq_one] at h1

/-- The homomorphism `H.map ϖ →* G` through which `f` factors, when `f` kills `H ∩ ker ϖ`. -/
noncomputable def descend (f : H →* G) (hf : ∀ h : H, ϖ h = 1 → f h = 1) : H.map ϖ →* G :=
  MonoidHom.mk' (fun q => f (mapPreimage ϖ q)) fun q q' => by
    show f (mapPreimage ϖ (q * q')) = f (mapPreimage ϖ q) * f (mapPreimage ϖ q')
    rw [← map_mul]
    refine descend_eq_of_map_eq ϖ f hf ?_
    simp only [Subgroup.coe_mul, map_mul, map_mapPreimage]

theorem descend_apply (f : H →* G) (hf : ∀ h : H, ϖ h = 1 → f h = 1) (h : H) :
    descend ϖ f hf ⟨ϖ h, Subgroup.mem_map_of_mem ϖ h.2⟩ = f h := by
  show f (mapPreimage ϖ ⟨ϖ h, Subgroup.mem_map_of_mem ϖ h.2⟩) = f h
  exact descend_eq_of_map_eq ϖ f hf (map_mapPreimage ϖ _)

theorem descend_unique (f : H →* G) (hf : ∀ h : H, ϖ h = 1 → f h = 1) (s : H.map ϖ →* G)
    (hs : ∀ h : H, s ⟨ϖ h, Subgroup.mem_map_of_mem ϖ h.2⟩ = f h) : s = descend ϖ f hf := by
  refine MonoidHom.ext fun q => ?_
  obtain ⟨y, hy⟩ := q
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact (hs ⟨x, hx⟩).trans (descend_apply ϖ f hf ⟨x, hx⟩).symm

/-- The image of a finite-index subgroup under a surjective homomorphism has finite index. -/
theorem finiteIndex_map_of_surjective (hϖ : Function.Surjective ϖ) [H.FiniteIndex] : (H.map ϖ).FiniteIndex :=
  ⟨ne_zero_of_dvd_ne_zero ‹H.FiniteIndex›.index_ne_zero (Subgroup.index_map_dvd H hϖ)⟩

/-- **Lemma 3.1, algebraic core.** Let `ϖ : E →* Q` be onto with kernel `⟨z⟩`, let `H ≤ E` have finite index, and let
`f : H →* G` kill the powers of `z` that lie in `H`. Then `H.map ϖ` has finite index, and `f` factors through it by a
unique homomorphism. -/
theorem lemma_3_1_descent (hϖ : Function.Surjective ϖ) {z : E} (hker : ϖ.ker = Subgroup.zpowers z)
    [H.FiniteIndex] (f : H →* G) (hf : ∀ (n : ℤ) (hn : z ^ n ∈ H), f ⟨z ^ n, hn⟩ = 1) :
    (H.map ϖ).FiniteIndex ∧ ∃! s : H.map ϖ →* G, ∀ h : H, s ⟨ϖ h, Subgroup.mem_map_of_mem ϖ h.2⟩ = f h := by
  have hf' : ∀ h : H, ϖ h = 1 → f h = 1 := by
    intro h hh
    have hmem : (h : E) ∈ Subgroup.zpowers z := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hh
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hz : z ^ n ∈ H := by
      rw [hn]
      exact h.2
    have heq : h = ⟨z ^ n, hz⟩ := Subtype.ext hn.symm
    rw [heq]
    exact hf n hz
  exact ⟨finiteIndex_map_of_surjective ϖ hϖ, descend ϖ f hf', descend_apply ϖ f hf',
    fun s hs => descend_unique ϖ f hf' s hs⟩

/-- **From Lemma 3.2 to the hypothesis of Lemma 3.3.** Suppose that
- every `α ∈ S` has a lift `α'` such that `f` sends every power of `α'` in `H` to a power of `α`;
- in `Q`, an element with a nonzero power equal to a power of some `α ∈ S` is itself a power of `α`.

Then the descended map sends every power of `α` in `H.map ϖ` to a power of `α`. -/
theorem descend_zpow_form [H.FiniteIndex] (f : H →* Q) (hf : ∀ h : H, ϖ h = 1 → f h = 1) {S : Set Q}
    (hroot : ∀ α ∈ S, ∀ (x : Q) (N : ℕ), N ≠ 0 → ∀ m : ℤ, x ^ N = α ^ m → ∃ m' : ℤ, x = α ^ m')
    (hlift : ∀ α ∈ S, ∃ α' : E, ϖ α' = α ∧ ∀ (e : ℤ) (he : α' ^ e ∈ H), ∃ m : ℤ, f ⟨α' ^ e, he⟩ = α ^ m) :
    ∀ α ∈ S, ∀ (k : ℤ) (hk : α ^ k ∈ H.map ϖ), ∃ m : ℤ, descend ϖ f hf ⟨α ^ k, hk⟩ = α ^ m := by
  intro α hα k hk
  obtain ⟨α', hα', hlift'⟩ := hlift α hα
  obtain ⟨j, hj0, -, hj⟩ := Subgroup.exists_pow_mem_of_index_ne_zero ‹H.FiniteIndex›.index_ne_zero (α' ^ k)
  have he : α' ^ (k * (j : ℤ)) ∈ H := by
    rwa [zpow_mul, zpow_natCast]
  obtain ⟨m, hm⟩ := hlift' (k * j) he
  refine hroot α hα _ j hj0.ne' m ?_
  have hpow : (⟨α ^ k, hk⟩ : H.map ϖ) ^ j =
      ⟨ϖ (⟨α' ^ (k * (j : ℤ)), he⟩ : H), Subgroup.mem_map_of_mem ϖ he⟩ := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow]
    show (α ^ k) ^ j = ϖ (α' ^ (k * (j : ℤ)))
    rw [map_zpow, hα', zpow_mul, zpow_natCast]
  rw [← map_pow, hpow]
  exact (descend_apply ϖ f hf ⟨α' ^ (k * (j : ℤ)), he⟩).trans hm

end GroupApproximation.BirmanGenusThree
