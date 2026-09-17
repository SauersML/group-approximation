import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group

/-!
# Elementary lemmas for the Hopf formula (lane LVHopf, leaf T1b.iv)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735: "Infinite finitely presented simple
Kazhdan groups exist [CapraceRemy]".  The repository reaches this sentence through
`K₂(4, L_{𝔽₂}(1,2)) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.1).  One step of that proof says that a
perfect central extension of a superperfect group is an isomorphism.  This lane proves it with the
Hopf formula `H₂(G; ℤ) ≅ (R ∩ [F,F]) / [F,R]`, in purely group-theoretic form.

This file collects the elementary facts used later:

* `mk'_mem_center_of_mem`: for a free presentation `R ↪ F ↠ G`, the image of `R` in `F/[F,R]` is
  central.
* `commutatorElement_mul_mul_of_mem_center`: the commutator bracket ignores central factors.
* `mk'_comp_eq_of_mem_commutator`: two lifts of the same map agree modulo `[F', ker g]` on `[F,F]`.
  This is the key to independence of presentation.
* `exists_freeGroup_lift`: free groups lift through surjections.
* `map_commutator_of_surjective`: surjections carry `[F,F]` onto `[F',F']`.

Everything is unconditional and uses only Mathlib.
-/

namespace GroupApproximation.Full.LVHopf

open scoped commutatorElement

universe u v w

section Quotients

variable {F : Type u} [Group F]

/-- `x` maps to `1` in `F ⧸ N` iff `x ∈ N`. -/
theorem mk'_eq_one_iff (N : Subgroup F) [N.Normal] (x : F) :
    QuotientGroup.mk' N x = 1 ↔ x ∈ N := by
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

/-- For a normal subgroup `N` (e.g. the relators `R`), the image of `N` in `F ⧸ [F, N]` is central.
(`simple_kazhdan_sofic_group.tex` l.733-735, Hopf formula.) -/
theorem mk'_mem_center_of_mem (N : Subgroup F) [N.Normal] {r : F} (hr : r ∈ N) :
    QuotientGroup.mk' ⁅(⊤ : Subgroup F), N⁆ r ∈
      Subgroup.center (F ⧸ ⁅(⊤ : Subgroup F), N⁆) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ⁅(⊤ : Subgroup F), N⁆ g
  have h1 : ⁅x, r⁆ ∈ ⁅(⊤ : Subgroup F), N⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hr
  have h2 := (mk'_eq_one_iff ⁅(⊤ : Subgroup F), N⁆ ⁅x, r⁆).mpr h1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

/-- The commutator bracket ignores central factors: `⁅a c, b d⁆ = ⁅a, b⁆` for central `c, d`. -/
theorem commutatorElement_mul_mul_of_mem_center (a b c d : F) (hc : c ∈ Subgroup.center F)
    (hd : d ∈ Subgroup.center F) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  calc ⁅a * c, b * d⁆ = a * (c * (b * d)) * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * (b * d * c) * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hc' (b * d)]
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hd' a⁻¹]
    _ = ⁅a, b⁆ := by group

/-- `⁅⊤, K⁆ ≤ [F, F]`. -/
theorem commutator_top_le_commutator (K : Subgroup F) :
    ⁅(⊤ : Subgroup F), K⁆ ≤ commutator F :=
  Subgroup.commutator_mono (le_refl _) le_top

end Quotients

/-- **Two lifts agree on `[F,F]` modulo `[F', ker g]`.**  If `φ ψ : F →* F'` satisfy
`g ∘ φ = g ∘ ψ`, then `φ x ≡ ψ x` modulo `⁅⊤, ker g⁆` for every `x ∈ [F, F]`.  The defect
`(φ a)⁻¹ ψ a` lies in `ker g`, whose image in `F' ⧸ [F', ker g]` is central, and the bracket
ignores central factors.  This yields independence of the Hopf multiplier from the presentation
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem mk'_comp_eq_of_mem_commutator {F : Type u} {F' : Type v} {G : Type w} [Group F]
    [Group F'] [Group G] (g : F' →* G) (φ ψ : F →* F') (h : g.comp φ = g.comp ψ) {x : F}
    (hx : x ∈ commutator F) :
    QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆ (φ x) =
      QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆ (ψ x) := by
  have hker : ∀ a : F, (φ a)⁻¹ * ψ a ∈ g.ker := by
    intro a
    have ha : g (φ a) = g (ψ a) := DFunLike.congr_fun h a
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel]
  have hc : ∀ a : F, QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆ ((φ a)⁻¹ * ψ a) ∈
      Subgroup.center (F' ⧸ ⁅(⊤ : Subgroup F'), g.ker⁆) :=
    fun a => mk'_mem_center_of_mem g.ker (hker a)
  have hψ : ∀ a : F, QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆ (ψ a) =
      QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆ (φ a) *
        QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆ ((φ a)⁻¹ * ψ a) := by
    intro a
    rw [← map_mul, mul_inv_cancel_left]
  have hEq : Set.EqOn ((QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆).comp φ)
      ((QuotientGroup.mk' ⁅(⊤ : Subgroup F'), g.ker⁆).comp ψ)
      {y : F | ∃ g₁ ∈ (⊤ : Subgroup F), ∃ g₂ ∈ (⊤ : Subgroup F), ⁅g₁, g₂⁆ = y} := by
    rintro y ⟨a, -, b, -, rfl⟩
    simp only [MonoidHom.comp_apply, map_commutatorElement]
    rw [hψ a, hψ b]
    exact (commutatorElement_mul_mul_of_mem_center _ _ _ _ (hc a) (hc b)).symm
  have hx' : x ∈ Subgroup.closure
      {y : F | ∃ g₁ ∈ (⊤ : Subgroup F), ∃ g₂ ∈ (⊤ : Subgroup F), ⁅g₁, g₂⁆ = y} := by
    rw [_root_.commutator_def, Subgroup.commutator_def] at hx
    exact hx
  exact MonoidHom.eqOn_closure hEq hx'

/-- **Free groups lift through surjections.** -/
theorem exists_freeGroup_lift {α : Type u} {G : Type v} {H : Type w} [Group G] [Group H]
    (f : FreeGroup α →* G) (p : H →* G) (hp : Function.Surjective p) :
    ∃ φ : FreeGroup α →* H, p.comp φ = f := by
  choose s hs using fun a : α => hp (f (FreeGroup.of a))
  refine ⟨FreeGroup.lift s, FreeGroup.ext_hom _ _ fun a => ?_⟩
  rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, hs a]

/-- A homomorphism carries `[F, F]` into `[F', F']`. -/
theorem map_commutator_le {F : Type u} {F' : Type v} [Group F] [Group F'] (φ : F →* F') :
    (commutator F).map φ ≤ commutator F' := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

/-- A surjection carries `[F, F]` onto `[F', F']`. -/
theorem map_commutator_of_surjective {F : Type u} {F' : Type v} [Group F] [Group F']
    (φ : F →* F') (hφ : Function.Surjective φ) : (commutator F).map φ = commutator F' := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective φ hφ]

/-- A surjection carries `⁅⊤, K⁆` onto `⁅⊤, K.map φ⁆`. -/
theorem map_commutator_top_of_surjective {F : Type u} {F' : Type v} [Group F] [Group F']
    (φ : F →* F') (hφ : Function.Surjective φ) (K : Subgroup F) :
    ⁅(⊤ : Subgroup F), K⁆.map φ = ⁅(⊤ : Subgroup F'), K.map φ⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ]

/-- The abelianization map is surjective. -/
theorem abelianization_of_surjective (G : Type u) [Group G] :
    Function.Surjective (Abelianization.of : G →* Abelianization G) :=
  fun z => QuotientGroup.mk'_surjective (commutator G) z

/-- `of x = 1` in the abelianization iff `x ∈ [G, G]`. -/
theorem abelianization_of_eq_one_iff {G : Type u} [Group G] (x : G) :
    (Abelianization.of x : Abelianization G) = 1 ↔ x ∈ commutator G := by
  rw [← MonoidHom.mem_ker, Abelianization.ker_of]

end GroupApproximation.Full.LVHopf
