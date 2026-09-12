import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Ping-pong families of group elements

A family `t₀, …, t_{n-1}` of elements of a group acting on a set `Ω` is a
*ping-pong family on `Ω`* when there are subsets `Aᵢ`, pairwise disjoint, and
`Bᵢ`, pairwise disjoint, with

    tᵢ • (Ω ∖ Aᵢ) ⊆ Bᵢ.

On `Ω = G` with left multiplication this is exactly what the `ℓ²` estimate of
`Analysis/PowersPingPongEstimate` consumes: `‖λ(t₀) + ⋯ + λ(t_{n-1})‖ ≤ 2√n`.
This module collects the purely set-theoretic ways of producing such families.

* `IsPingPongOn.isPingPongFamily` — a ping-pong family on **any** `G`-set pulls
  back to one on `G` along an orbit map; no faithfulness is needed.
* `IsPingPongFamily.mul_right` — a common right factor is absorbed.
* `IsPingPongFamily.map_mulEquiv`, `IsPingPongFamily.subtype`,
  `IsPingPongFamily.map_of_injective` — a family in a subgroup, or in the source
  of an injective homomorphism, is a family in the ambient group.  The subgroup
  case lifts the sets along a choice of right-coset representatives
  (`rightComponent`).
* `isPingPongOn_conj_pow` — the conjugates `yⁱ f y⁻ⁱ` form a ping-pong family
  on `Ω` as soon as there are disjoint `X₁`, `X₂` with `yᵏ • X₁ ⊆ X₂` for
  `k ≠ 0` and `f⁻¹ • (Ω ∖ X₁) ⊆ X₁`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (simplicity and uniqueness of the
trace, through Powers averaging); certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace PingPongTranslates

open scoped Pointwise

universe u v

section Action

variable {K : Type u} [Group K] (Ω : Type v) [MulAction K Ω]

/-- **A ping-pong family on a `K`-set `Ω`**: pairwise disjoint `Aᵢ`, pairwise
disjoint `Bᵢ`, and `tᵢ • (Ω ∖ Aᵢ) ⊆ Bᵢ`. -/
def IsPingPongOn {n : ℕ} (t : Fin n → K) : Prop :=
  ∃ A B : Fin n → Set Ω, (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ ∀ i, t i • (A i)ᶜ ⊆ B i

end Action

variable {G : Type u} [Group G]

/-- **A ping-pong family in `G`**: a ping-pong family on `G` acting on itself by
left multiplication. -/
def IsPingPongFamily {n : ℕ} (t : Fin n → G) : Prop :=
  IsPingPongOn G t

/-! ## Pulling back along an orbit map -/

/-- **A ping-pong family on any `G`-set is a ping-pong family in `G`.**  The sets
are the preimages under `g ↦ g • ω₀`; the action need not be faithful. -/
theorem IsPingPongOn.isPingPongFamily {Ω : Type v} [MulAction G Ω] (ω₀ : Ω) {n : ℕ}
    {t : Fin n → G} (h : IsPingPongOn Ω t) : IsPingPongFamily t := by
  unfold IsPingPongOn at h
  unfold IsPingPongFamily IsPingPongOn
  obtain ⟨A, B, hA, hB, hmap⟩ := h
  refine ⟨fun i ↦ (fun g : G ↦ g • ω₀) ⁻¹' A i, fun i ↦ (fun g : G ↦ g • ω₀) ⁻¹' B i,
    fun i j hij ↦ (hA i j hij).preimage _, fun i j hij ↦ (hB i j hij).preimage _, ?_⟩
  intro i x hx
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
  have hx' : ((t i)⁻¹ * x) • ω₀ ∉ A i := hx
  show x • ω₀ ∈ B i
  apply hmap i
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rw [mul_smul] at hx'
  exact hx'

/-! ## A common right factor -/

/-- **A common right factor is absorbed**: if `(tᵢ)` is a ping-pong family, so is
`(tᵢ γ)`, with the sets `Aᵢ` translated by `γ⁻¹`. -/
theorem IsPingPongFamily.mul_right {n : ℕ} {t : Fin n → G} (h : IsPingPongFamily t)
    (γ : G) : IsPingPongFamily (fun i ↦ t i * γ) := by
  unfold IsPingPongFamily IsPingPongOn at h ⊢
  obtain ⟨A, B, hA, hB, hmap⟩ := h
  refine ⟨fun i ↦ (fun x : G ↦ γ * x) ⁻¹' A i, B,
    fun i j hij ↦ (hA i j hij).preimage _, hB, ?_⟩
  intro i x hx
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
  have hx' : γ * ((t i * γ)⁻¹ * x) ∉ A i := hx
  have heq : γ * ((t i * γ)⁻¹ * x) = (t i)⁻¹ * x := by group
  rw [heq] at hx'
  apply hmap i
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  exact hx'

/-! ## Transport along isomorphisms, subgroups, and injective homomorphisms -/

/-- **Transport along a group isomorphism.** -/
theorem IsPingPongFamily.map_mulEquiv {H : Type v} [Group H] (e : G ≃* H) {n : ℕ}
    {t : Fin n → G} (h : IsPingPongFamily t) : IsPingPongFamily (fun i ↦ e (t i)) := by
  unfold IsPingPongFamily IsPingPongOn at h ⊢
  obtain ⟨A, B, hA, hB, hmap⟩ := h
  refine ⟨fun i ↦ e.symm ⁻¹' A i, fun i ↦ e.symm ⁻¹' B i,
    fun i j hij ↦ (hA i j hij).preimage _, fun i j hij ↦ (hB i j hij).preimage _, ?_⟩
  intro i x hx
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
  have hx' : e.symm ((e (t i))⁻¹ * x) ∉ A i := hx
  rw [map_mul, map_inv, MulEquiv.symm_apply_apply] at hx'
  show e.symm x ∈ B i
  apply hmap i
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  exact hx'

/-- **The `H`-component of an element**: `x · r⁻¹`, where `r` is the chosen
representative of the right coset `H x`. -/
noncomputable def rightComponent (H : Subgroup G) (x : G) : H :=
  ⟨x * (Quotient.mk (QuotientGroup.rightRel H) x).out⁻¹,
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel H) x)⟩

/-- **The `H`-component is `H`-equivariant**: `comp(h x) = h · comp(x)` for
`h ∈ H`, because `h x` and `x` lie in the same right coset. -/
theorem rightComponent_mul (H : Subgroup G) (h : H) (x : G) :
    rightComponent H ((h : G) * x) = h * rightComponent H x := by
  have hq : Quotient.mk (QuotientGroup.rightRel H) ((h : G) * x)
      = Quotient.mk (QuotientGroup.rightRel H) x := by
    apply Quotient.sound
    show QuotientGroup.rightRel H ((h : G) * x) x
    rw [QuotientGroup.rightRel_apply, mul_inv_rev, mul_inv_cancel_left]
    exact H.inv_mem h.2
  apply Subtype.ext
  show (h : G) * x * (Quotient.mk (QuotientGroup.rightRel H) ((h : G) * x)).out⁻¹
      = (h : G) * (x * (Quotient.mk (QuotientGroup.rightRel H) x).out⁻¹)
  rw [hq, mul_assoc]

/-- **A ping-pong family in a subgroup is a ping-pong family in the group.**  The
sets are pulled back along `rightComponent`. -/
theorem IsPingPongFamily.subtype {H : Subgroup G} {n : ℕ} {t : Fin n → H}
    (h : IsPingPongFamily t) : IsPingPongFamily (fun i ↦ (t i : G)) := by
  unfold IsPingPongFamily IsPingPongOn at h ⊢
  obtain ⟨A, B, hA, hB, hmap⟩ := h
  refine ⟨fun i ↦ rightComponent H ⁻¹' A i, fun i ↦ rightComponent H ⁻¹' B i,
    fun i j hij ↦ (hA i j hij).preimage _, fun i j hij ↦ (hB i j hij).preimage _, ?_⟩
  intro i x hx
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
  have hx' : rightComponent H (((t i)⁻¹ : H) * x) ∉ A i := hx
  rw [rightComponent_mul] at hx'
  show rightComponent H x ∈ B i
  apply hmap i
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  exact hx'

/-- **Push forward along an injective homomorphism.** -/
theorem IsPingPongFamily.map_of_injective {H : Type u} [Group H] (φ : H →* G)
    (hφ : Function.Injective φ) {n : ℕ} {t : Fin n → H} (h : IsPingPongFamily t) :
    IsPingPongFamily (fun i ↦ φ (t i)) := by
  have h₁ := (h.map_mulEquiv (MonoidHom.ofInjective hφ)).subtype
  simpa only [MonoidHom.ofInjective_apply] using h₁

/-! ## Conjugates by powers -/

/-- **The conjugates `yⁱ f y⁻ⁱ` (`0 ≤ i < n`) form a ping-pong family on `Ω`**,
given disjoint `X₁`, `X₂` with `yᵏ • X₁ ⊆ X₂` for every `k ≠ 0` and
`f⁻¹ • (Ω ∖ X₁) ⊆ X₁`.  The sets are `Aᵢ = yⁱ f⁻¹ • (Ω ∖ X₁)` and `Bᵢ = yⁱ • X₁`;
the mapping condition holds with equality, and both disjointness conditions
reduce to: `y⁻ⁱ x` and `y⁻ʲ x` cannot both lie in `X₁` for `i ≠ j`. -/
theorem isPingPongOn_conj_pow {K : Type u} [Group K] {Ω : Type v} [MulAction K Ω]
    (f y : K) (X₁ X₂ : Set Ω) (hdisj : Disjoint X₁ X₂)
    (hy : ∀ k : ℤ, k ≠ 0 → y ^ k • X₁ ⊆ X₂) (hf : f⁻¹ • X₁ᶜ ⊆ X₁) (n : ℕ) :
    IsPingPongOn Ω (fun i : Fin n ↦ y ^ (i : ℕ) * f * (y ^ (i : ℕ))⁻¹) := by
  have key : ∀ i j : ℕ, i ≠ j → ∀ x : Ω,
      (y ^ i)⁻¹ • x ∈ X₁ → (y ^ j)⁻¹ • x ∈ X₁ → False := by
    intro i j hij x hi hj
    have hk : ((j : ℤ) - (i : ℤ)) ≠ 0 := by
      intro h0
      apply hij
      omega
    have h2 := hy ((j : ℤ) - (i : ℤ)) hk (Set.smul_mem_smul_set_iff.mpr hj)
    have heq : y ^ ((j : ℤ) - (i : ℤ)) • (y ^ j)⁻¹ • x = (y ^ i)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      simp only [zpow_sub, zpow_natCast]
      group
    rw [heq] at h2
    exact Set.disjoint_left.mp hdisj hi h2
  unfold IsPingPongOn
  refine ⟨fun i ↦ (y ^ (i : ℕ) * f⁻¹) • X₁ᶜ, fun i ↦ y ^ (i : ℕ) • X₁, ?_, ?_, ?_⟩
  · intro i j hij
    show Disjoint ((y ^ (i : ℕ) * f⁻¹) • X₁ᶜ) ((y ^ (j : ℕ) * f⁻¹) • X₁ᶜ)
    refine Set.disjoint_left.mpr fun x hxi hxj ↦ ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hxi hxj
    have hi := hf (Set.smul_mem_smul_set_iff.mpr hxi)
    have hj := hf (Set.smul_mem_smul_set_iff.mpr hxj)
    rw [smul_smul, show f⁻¹ * (y ^ (i : ℕ) * f⁻¹)⁻¹ = (y ^ (i : ℕ))⁻¹ by group] at hi
    rw [smul_smul, show f⁻¹ * (y ^ (j : ℕ) * f⁻¹)⁻¹ = (y ^ (j : ℕ))⁻¹ by group] at hj
    exact key i j (fun h ↦ hij (Fin.ext h)) x hi hj
  · intro i j hij
    show Disjoint (y ^ (i : ℕ) • X₁) (y ^ (j : ℕ) • X₁)
    refine Set.disjoint_left.mpr fun x hxi hxj ↦ ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hxi hxj
    exact key i j (fun h ↦ hij (Fin.ext h)) x hxi hxj
  · intro i x hx
    have hx' : x ∈ (y ^ (i : ℕ) * f * (y ^ (i : ℕ))⁻¹) •
        ((y ^ (i : ℕ) * f⁻¹) • X₁ᶜ)ᶜ := hx
    show x ∈ y ^ (i : ℕ) • X₁
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx' ⊢
    rw [Set.mem_compl_iff, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_compl_iff, not_not,
      smul_smul] at hx'
    rw [show (y ^ (i : ℕ) * f⁻¹)⁻¹ * (y ^ (i : ℕ) * f * (y ^ (i : ℕ))⁻¹)⁻¹
        = (y ^ (i : ℕ))⁻¹ by group] at hx'
    exact hx'

end PingPongTranslates
end GroupApproximation

open GroupApproximation.PingPongTranslates

#audit_axioms IsPingPongOn
#audit_axioms IsPingPongFamily
#audit_axioms IsPingPongOn.isPingPongFamily
#audit_axioms IsPingPongFamily.mul_right
#audit_axioms IsPingPongFamily.map_mulEquiv
#audit_axioms rightComponent
#audit_axioms rightComponent_mul
#audit_axioms IsPingPongFamily.subtype
#audit_axioms IsPingPongFamily.map_of_injective
#audit_axioms isPingPongOn_conj_pow
