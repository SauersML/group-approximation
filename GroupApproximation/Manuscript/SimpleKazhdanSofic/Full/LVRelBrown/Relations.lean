import Mathlib.Tactic.Group
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRelBrown.VertexSection
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.EdgeRelation

/-!
# Brown's relations inside `Ψ`-images, and the relative retraction

This file belongs to the relative rank-four Brown criterion (Khanh, arXiv:2609.08428, Thm 5.1),
which is used on the Leavitt route to `simple_kazhdan_sofic_group.tex` l.733-735
(`sec:questions`).

Let `Ψ : St_4(L) →* Q` be a homomorphism, and let `σ : J →* Q` send `1 + E_{ij}(a)` (`j ≠ 3`) to
`Ψ (x_{ij}(a))` (`RelLiftsRoots`, satisfied by `relSection`). Put `t = Ψ (w₃₂)`. This file proves
the relative versions of the `LVAssembly` glue.

* `relEdgeRelation`: `t σ(k) t⁻¹ = σ(τ k τ⁻¹)` for `k ∈ J ∩ Stab(e₂)`. This is the image under `Ψ`
  of the Weyl conjugation `weylLast_conj_x`, extended over the closure of the edge generators.
* `relTriangleRelation`: `t σ(h) t = σ(h) t σ(h)`, the image of `weyl_braid`.
* `relSquare`: `t² = σ(τ²) = 1`, the image of `w₃₂² = 1` (`weyl_mul_self`).
* `relLift_projection_eq`: if `F : GL_4(L) →* Q` extends `σ` with `F τ = t`, then
  `F ∘ projection = Ψ`.

With `Q = St_4(L)` and `Ψ = id`, these are `LVAssembly.edgeRelation_of_liftsRoots`,
`LVAssembly.triangleRelation_of_liftsRoots` and `LVAssembly.lift_projection_eq`.
-/

namespace GroupApproximation
namespace Full
namespace LVRelBrown

open SteinbergGroup LVAssembly
open scoped Matrix

noncomputable section

/-- **Relative root lift**: `σ (1 + E_{ij}(a)) = Ψ (x_{ij}(a))` for `j ≠ 3` (Khanh, Thm 5.1). -/
def RelLiftsRoots {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (σ : vertexStab →* Q) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (hj : j ≠ 3) (a : BinL),
    σ ⟨elementaryUnit i j hij a, elementaryUnit_mem_vertexStab i j hij hj a⟩ = Ψ (x i j hij a)

/-- The relative vertex section lifts the roots. -/
theorem relSection_relLiftsRoots {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (hΨ : ∀ k : SteinbergGroup (Fin 3) BinL, projection k = 1 →
      Ψ (LVCentral.castSuccStab 3 BinL k) = 1) :
    RelLiftsRoots Ψ (relSection Ψ hΨ) :=
  fun i j hij hj a => relSection_elementaryUnit Ψ hΨ i j hij hj a

section Edge

variable {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q) (σ : vertexStab →* Q)

/-- On a generator, the relative edge relation is the image of Weyl conjugation. -/
theorem relEdge_gen (hσ : RelLiftsRoots Ψ σ) (p q : Fin 4) (hpq : p ≠ q) (c : BinL)
    (hq : q.val < 2) (h1 : elementaryUnit p q hpq c ∈ vertexStab)
    (h2 : swapLast * elementaryUnit p q hpq c * swapLast⁻¹ ∈ vertexStab) :
    Ψ weylLast * σ ⟨elementaryUnit p q hpq c, h1⟩ * (Ψ weylLast)⁻¹ =
      σ ⟨swapLast * elementaryUnit p q hpq c * swapLast⁻¹, h2⟩ := by
  have hq3 : q ≠ 3 := ne_three_of_lt_two hq
  have hsq : Equiv.swap (3 : Fin 4) 2 q = q :=
    Equiv.swap_apply_of_ne_of_ne hq3 (ne_two_of_lt_two hq)
  have hq3' : Equiv.swap (3 : Fin 4) 2 q ≠ 3 := by rw [hsq]; exact hq3
  have e2 : (⟨swapLast * elementaryUnit p q hpq c * swapLast⁻¹, h2⟩ : vertexStab) =
      ⟨elementaryUnit (Equiv.swap (3 : Fin 4) 2 p) (Equiv.swap (3 : Fin 4) 2 q)
        ((Equiv.swap (3 : Fin 4) 2).injective.ne hpq) c,
        elementaryUnit_mem_vertexStab _ _ _ hq3' c⟩ :=
    Subtype.ext (swapLast_conj_elementaryUnit p q hpq c)
  rw [e2, hσ p q hpq hq3 c, hσ _ _ _ hq3' c]
  have hc := congrArg Ψ (weylLast_conj_x p q hpq c)
  simp only [map_mul, map_inv] at hc
  exact hc

/-- **The relative edge relation on the closure of the edge generators.** -/
theorem relEdge_aux (hσ : RelLiftsRoots Ψ σ) {g : GLFour}
    (hg : g ∈ Subgroup.closure (edgeGens BinL)) :
    ∀ (h1 : g ∈ vertexStab) (h2 : swapLast * g * swapLast⁻¹ ∈ vertexStab),
      Ψ weylLast * σ ⟨g, h1⟩ * (Ψ weylLast)⁻¹ = σ ⟨swapLast * g * swapLast⁻¹, h2⟩ := by
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨p, q, hpq, c, hq, rfl⟩ := hz
    exact relEdge_gen Ψ σ hσ p q hpq c hq
  | one =>
    intro h1 h2
    have e0 : (⟨1, h1⟩ : vertexStab) = 1 := rfl
    have e1 : (⟨swapLast * 1 * swapLast⁻¹, h2⟩ : vertexStab) = 1 :=
      Subtype.ext (show swapLast * 1 * swapLast⁻¹ = 1 by rw [mul_one, mul_inv_cancel])
    rw [e0, e1, map_one σ, mul_one, mul_inv_cancel]
  | mul a b ha hb iha ihb =>
    intro h1 h2
    have haJ := closure_le_vertexStab ha
    have hbJ := closure_le_vertexStab hb
    have ha' := closure_le_vertexStab (conj_mem_closure ha)
    have hb' := closure_le_vertexStab (conj_mem_closure hb)
    have e1 : (⟨a * b, h1⟩ : vertexStab) = (⟨a, haJ⟩ : vertexStab) * (⟨b, hbJ⟩ : vertexStab) :=
      rfl
    have e2 : (⟨swapLast * (a * b) * swapLast⁻¹, h2⟩ : vertexStab) =
        (⟨swapLast * a * swapLast⁻¹, ha'⟩ : vertexStab) *
          (⟨swapLast * b * swapLast⁻¹, hb'⟩ : vertexStab) :=
      Subtype.ext (show swapLast * (a * b) * swapLast⁻¹ =
        swapLast * a * swapLast⁻¹ * (swapLast * b * swapLast⁻¹) by group)
    rw [e1, e2, map_mul σ, map_mul σ, ← iha haJ ha', ← ihb hbJ hb']
    group
  | inv a ha ih =>
    intro h1 h2
    have haJ := closure_le_vertexStab ha
    have ha' := closure_le_vertexStab (conj_mem_closure ha)
    have e1 : (⟨a⁻¹, h1⟩ : vertexStab) = (⟨a, haJ⟩ : vertexStab)⁻¹ := rfl
    have e2 : (⟨swapLast * a⁻¹ * swapLast⁻¹, h2⟩ : vertexStab) =
        (⟨swapLast * a * swapLast⁻¹, ha'⟩ : vertexStab)⁻¹ :=
      Subtype.ext (show swapLast * a⁻¹ * swapLast⁻¹ = (swapLast * a * swapLast⁻¹)⁻¹ by group)
    rw [e1, e2, map_inv σ, map_inv σ, ← ih haJ ha']
    group

/-- **Brown's edge relation inside `Ψ`-images**, with `t = Ψ (w₃₂)` (Khanh, Thm 5.1;
tex l.733-735). -/
theorem relEdgeRelation (hσ : RelLiftsRoots Ψ σ) :
    ∀ k k' : vertexStab, ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ prevCol = prevCol →
      (k' : GLFour) = swapLast * (k : GLFour) * swapLast⁻¹ →
        Ψ weylLast * σ k * (Ψ weylLast)⁻¹ = σ k' := by
  rintro ⟨g, hg⟩ ⟨g', hg'⟩ hk hk'
  have hg3 : (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 3 1 = Pi.single 3 1 := hg
  have hg2 : (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 2 1 = Pi.single 2 1 := hk
  have hK : g ∈ edgeStab BinL :=
    mem_edgeStab.mpr ⟨mem_columnFixer.mpr ((mulVec_single_iff _ 3).mp hg3),
      mem_columnFixer.mpr ((mulVec_single_iff _ 2).mp hg2)⟩
  have hcl : g ∈ Subgroup.closure (edgeGens BinL) := edgeStab_le_closure hE2L hK
  have hk'' : g' = swapLast * g * swapLast⁻¹ := hk'
  subst hk''
  exact relEdge_aux Ψ σ hσ hcl hg hg'

end Edge

section Triangle

variable {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q) (σ : vertexStab →* Q)

/-- A relative root lift sends `h = swapMid` to `Ψ (w₂₁)`. -/
theorem relSigma_swapMid (hσ : RelLiftsRoots Ψ σ) (j : vertexStab)
    (hj : (j : GLFour) = swapMid) :
    σ j = Ψ (GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl (R := BinL)
      (2 : Fin 4) 1 midIdx_ne) := by
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have hA := elementaryUnit_mem_vertexStab (2 : Fin 4) 1 midIdx_ne h13 (1 : BinL)
  have hB := elementaryUnit_mem_vertexStab (1 : Fin 4) 2 midIdx_ne.symm h23 (1 : BinL)
  have hj' : j =
      (⟨elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL), hA⟩ : vertexStab) *
      ⟨elementaryUnit (1 : Fin 4) 2 midIdx_ne.symm (1 : BinL), hB⟩ *
      ⟨elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL), hA⟩ :=
    Subtype.ext (hj.trans swapMid_eq)
  have hw : Ψ (GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl (R := BinL)
      (2 : Fin 4) 1 midIdx_ne) =
      Ψ (x (2 : Fin 4) 1 midIdx_ne (1 : BinL)) * Ψ (x (1 : Fin 4) 2 midIdx_ne.symm (1 : BinL)) *
        Ψ (x (2 : Fin 4) 1 midIdx_ne (1 : BinL)) := by
    rw [GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl, map_mul Ψ, map_mul Ψ]
  rw [hj', map_mul σ, map_mul σ, hσ (2 : Fin 4) 1 midIdx_ne h13 (1 : BinL),
    hσ (1 : Fin 4) 2 midIdx_ne.symm h23 (1 : BinL), hw]

/-- **Brown's triangle relation inside `Ψ`-images**, with `t = Ψ (w₃₂)` (Khanh, Thm 5.1;
tex l.733-735). -/
theorem relTriangleRelation (hσ : RelLiftsRoots Ψ σ) (j : vertexStab)
    (hj : (j : GLFour) = swapMid) :
    Ψ weylLast * σ j * Ψ weylLast = σ j * Ψ weylLast * σ j := by
  rw [relSigma_swapMid Ψ σ hσ j hj]
  have hb := congrArg Ψ (weyl_braid (n := 4) two_eq_zero_binL (by decide) lastIdx_ne midIdx_ne
    (show (3 : Fin 4) ≠ 1 by decide))
  simp only [map_mul] at hb
  exact hb

end Triangle

/-- `w₃₂² = 1` in `St_4(L)`, since `L` has characteristic two. -/
theorem weylLast_mul_weylLast : weylLast * weylLast = 1 :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_mul_self (R := BinL)
    two_eq_zero_binL (3 : Fin 4) 2 lastIdx_ne

/-- `τ² = 1` in `GL_4(L)`: the image of `w₃₂² = 1`. -/
theorem swapLast_mul_swapLast : swapLast * swapLast = 1 := by
  have hc := congrArg
    (fun g => ((projection g : elementaryGroup (Fin 4) BinL) : GLFour)) weylLast_mul_weylLast
  simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at hc
  exact hc

/-- **Brown's square relation inside `Ψ`-images**: `t² = σ(τ²)` with `t = Ψ (w₃₂)`
(Khanh, Thm 5.1). -/
theorem relSquare {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (σ : vertexStab →* Q) (h : swapLast * swapLast ∈ vertexStab) :
    Ψ weylLast * Ψ weylLast = σ ⟨swapLast * swapLast, h⟩ := by
  have e : (⟨swapLast * swapLast, h⟩ : vertexStab) = 1 := Subtype.ext swapLast_mul_swapLast
  rw [e, map_one σ, ← map_mul Ψ, weylLast_mul_weylLast, map_one Ψ]

/-- **The relative retraction** (Khanh, Thm 5.1; tex l.733-735). If `F : GL_4(L) →* Q` extends a
relative root lift `σ` and `F τ = Ψ (w₃₂)`, then `F ∘ projection = Ψ`. -/
theorem relLift_projection_eq {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (σ : vertexStab →* Q) (F : GLFour →* Q) (hroot : RelLiftsRoots Ψ σ)
    (hFJ : ∀ j : vertexStab, F (j : GLFour) = σ j) (hFτ : F swapLast = Ψ weylLast)
    (g : SteinbergGroup (Fin 4) BinL) :
    F ((projection g : elementaryGroup (Fin 4) BinL) : GLFour) = Ψ g := by
  have hS : (F.comp ((elementaryGroup (Fin 4) BinL).subtype.comp
      (projection (I := Fin 4) (R := BinL)))).eqLocus Ψ = ⊤ := by
    refine steinberg_eq_top_of_mem _ ?_ ?_
    · intro i j hij hj a
      show F ((projection (x i j hij a) : elementaryGroup (Fin 4) BinL) : GLFour) =
        Ψ (x i j hij a)
      rw [projection_x]
      exact (hFJ ⟨elementaryUnit i j hij a, elementaryUnit_mem_vertexStab i j hij hj a⟩).trans
        (hroot i j hij hj a)
    · show F swapLast = Ψ weylLast
      exact hFτ
  have hg : g ∈ (F.comp ((elementaryGroup (Fin 4) BinL).subtype.comp
      (projection (I := Fin 4) (R := BinL)))).eqLocus Ψ := by
    rw [hS]
    exact Subgroup.mem_top g
  exact hg

end

end LVRelBrown
end Full
end GroupApproximation
