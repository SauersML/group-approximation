import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityAssembly
import GroupApproximation.Leavitt.ElementaryNormalGeneration
import Mathlib.GroupTheory.Commutator.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:general` (a): simplicity of `EL_n(LC(C, F₂) ⋊ Λ)`, with Steps 1–3 of its proof

`simple_kazhdan_sofic_group.tex`, `thm:general` (a) (tex l.172–177), simplicity clause, and
`sec:proof`, subsection "Simplicity" (tex l.241–315), Steps 1, 2 and 3.

The printed ring `R = LC(C, F₂) ⋊ Λ` is `SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ`, with
the action on coefficients `(ξ • f)(z) = f(ξ⁻¹ z)` (hypothesis `hact`); the ring
`ClopenGroupCrossedProduct Λ Z (ZMod 2)` of `thm:general` is this ring with `hact` holding by `rfl`.
The printed `e_V` is `SkewMonoidAlgebra.single 1 (LocallyConstant.charFn (ZMod 2) hV)`, i.e.
`General.coeffHom Λ Z (charFn V)`, and `u_ξ = General.unitHom Λ Z ξ`.

* **The theorem.** `generalSimple`, `generalSimple_printed`: `EL_n(R)` is simple for `n ≥ 3`, for a
  minimal topologically free action on a Cantor set (finite generation of `Λ` and perfectness of
  `C` are not used for simplicity).
* **Step 1** (tex l.245–274). Small sets exist (`stepOne_smallSets`, `stepOne_movedPointsDense`);
  some `h = e_ij(e_V)` with `V` small does not commute with `g` (`stepOne_nonCommutingRoot`), and
  `x = [g, h]` lies in `K ∖ {1}` (`stepOne_commutator`). The printed balls `B_{2w}`, `B_w` and the
  finitely many coefficients of the entries of `g` are arbitrary finite sets `D`, `B`, `F` here.
* **Step 2** (tex l.276–306). `ε_ab ε_a'b' = δ_ba' ε_ab'` (`stepTwo_epsilon_mul_epsilon`),
  `ε_ab ≠ 0` (`stepTwo_epsilon_ne_zero`), `A_V ≅ M_B(F₂)` (`stepTwo_ringCopy`), the embedding of
  `GL_{ι × B}(F₂)` with image `H_V ⊆ G` and every `k` with `k - I, k⁻¹ - I ∈ M_ι(A_V)` in `H_V`
  (`stepTwo_towerCopy`), `A_V` is closed under products (`stepTwo_epsilonSpan_mul_mem`), the
  displayed products `f u_a e_V f' u_b ∈ A_V` (`stepTwo_mul_charFn_mul_mem`), the simplicity of
  `GL_d(F₂)`, `d ≥ 3` (`stepTwo_glSimple`), and the conclusion: every nontrivial normal subgroup
  contains the commutator witness (`stepTwo_commutatorWitness`).
* **Step 3** (tex l.308–315). `J` is the two-sided ideal `levelIdeal` (`stepThree_levelIdeal`), it
  contains `e_{ξV} = u_ξ e_V u_ξ⁻¹` (`stepThree_charFn_smul_mem`), finitely many `ξV` cover `C`
  (`stepThree_finiteCover`), `1 ∈ J` (`stepThree_one_mem`), `1 ∈ J` gives `K = G`
  (`stepThree_eq_top_of_one_mem`), and the whole of Steps 2–3 from the witness
  (`stepThree_normalSubgroupEqTop`).
-/

namespace GroupApproximation.Full.SK02

open scoped Pointwise
open GroupApproximation.Pestov91.SimpleModCentre

/-! ### The theorem -/

/-- **`thm:general` (a), simplicity** (tex l.172–177, proof tex l.241–315): for a minimal,
topologically free action by homeomorphisms on a nonempty compact totally separated space, and every
`n ≥ 3`, `EL_n(LC(Z, F₂) ⋊ Λ)` is simple. -/
theorem generalSimple {Λ Z : Type*} [Group Λ] [TopologicalSpace Z]
    [MulAction Λ Z] [ContinuousConstSMul Λ Z] [CompactSpace Z] [TotallySeparatedSpace Z]
    [Nonempty Z] [MulAction.IsMinimal Λ Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :=
  SimpleKazhdanSofic.General.isSimpleGroup_clopenGroupCrossedProduct hfree hn

/-- **`thm:general` (a), simplicity, with the printed hypotheses** (tex l.166–177): `C` is a
nonempty compact metrizable totally disconnected space (a Cantor set is one), the action is minimal,
and no nontrivial element fixes a nonempty open set. -/
theorem generalSimple_printed {Λ Z : Type*} [Group Λ]
    [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z] [CompactSpace Z]
    [TopologicalSpace.MetrizableSpace Z] [TotallyDisconnectedSpace Z] [Nonempty Z]
    (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :=
  SimpleKazhdanSofic.General.isSimpleGroup_clopenGroupCrossedProduct_of_isOpen hmin hfree hn

/-! ### Step 1: a nontrivial commutator with a small elementary matrix -/

section StepOne

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]

/-- **Step 1, tex l.253–255**: each `ξ ≠ e` fixes a closed set with empty interior, so the points
moved by every `ξ ∈ D ∖ {e}` form a dense set. -/
theorem stepOne_movedPointsDense [T2Space Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D : Finset Λ) :
    Dense {z : Z | ∀ ξ ∈ D, ξ ≠ 1 → ξ • z ≠ z} :=
  SimpleKazhdanSofic.General.dense_moved hfree D

/-- **Step 1, tex l.248–257**: every nonempty clopen set contains a nonempty small one, where `V` is
small if `V ∩ ξV = ∅` for `ξ ∈ D ∖ {e}` and `f ∘ ξ` is constant on `V` for `ξ ∈ B`, `f ∈ F`. -/
theorem stepOne_smallSets [TotallySeparatedSpace Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {A : Set Z} (hA : IsClopen A) (hne : A.Nonempty) :
    ∃ V : Set Z, IsClopen V ∧ V.Nonempty ∧ V ⊆ A ∧ SimpleKazhdanSofic.General.IsSmall D B F V :=
  SimpleKazhdanSofic.General.exists_isSmall_subset hfree D B F hA hne

/-- **Step 1, tex l.271–274**: if `g ∈ K` does not commute with `h`, then `x = [g, h]` lies in
`K ∖ {1}`. -/
theorem commutator_mem_ne_one {G : Type*} [Group G] {K : Subgroup G} (hK : K.Normal) {g h : G}
    (hg : g ∈ K) (hgh : ¬ Commute g h) :
    g * h * g⁻¹ * h⁻¹ ∈ K ∧ g * h * g⁻¹ * h⁻¹ ≠ 1 := by
  refine ⟨?_, fun h1 => hgh ?_⟩
  · have e : g * h * g⁻¹ * h⁻¹ = g * (h * g⁻¹ * h⁻¹) := by simp only [mul_assoc]
    rw [e]
    exact K.mul_mem hg (hK.conj_mem g⁻¹ (K.inv_mem hg) h)
  · show g * h = h * g
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)

variable [TotallySeparatedSpace Z] [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]

/-- **Step 1, tex l.258–271**: for `1 ≠ g ∈ EL_n(R)`, `n ≥ 2`, whose entries are supported in `D`,
some `h = e_ij(e_V)` with `V` small and nonempty does not commute with `g`. -/
theorem stepOne_nonCommutingRoot
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {n : ℕ} (hn : 2 ≤ n)
    {g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)}
    (hD : ∀ (p q : Fin n) (ξ : Λ),
      ξ ∈ SkewMonoidAlgebra.support (SimpleKazhdanSofic.General.mat g p q) → ξ ∈ D)
    (hg1 : g ≠ 1) :
    ∃ (V : Set Z) (hV : IsClopen V), V.Nonempty ∧ SimpleKazhdanSofic.General.IsSmall D B F V ∧
      ∃ (i j : Fin n) (hij : i ≠ j),
        ¬ Commute g
          (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) :=
  SimpleKazhdanSofic.General.exists_isSmall_not_commute_elGen hact hfree D B F hn hD hg1

/-- **Step 1, as printed** (tex l.243–274): for `1 ≠ g ∈ K ⊴ EL_n(R)`, some `h = e_ij(e_V)` with `V`
small and nonempty gives `x = [g, h] ∈ K ∖ {1}`. -/
theorem stepOne_commutator
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {n : ℕ} (hn : 2 ≤ n)
    {K : Subgroup (elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))}
    (hK : K.Normal)
    {g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)} (hgK : g ∈ K)
    (hD : ∀ (p q : Fin n) (ξ : Λ),
      ξ ∈ SkewMonoidAlgebra.support (SimpleKazhdanSofic.General.mat g p q) → ξ ∈ D)
    (hg1 : g ≠ 1) :
    ∃ (V : Set Z) (hV : IsClopen V), V.Nonempty ∧ SimpleKazhdanSofic.General.IsSmall D B F V ∧
      ∃ (i j : Fin n) (hij : i ≠ j),
        g * elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
            g⁻¹ *
            (elGen i j hij
              (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)))⁻¹ ∈ K ∧
          g * elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) *
            g⁻¹ *
            (elGen i j hij
              (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)))⁻¹ ≠ 1 := by
  obtain ⟨V, hV, hVne, hs, i, j, hij, hc⟩ :=
    SimpleKazhdanSofic.General.exists_isSmall_not_commute_elGen hact hfree D B F hn hD hg1
  exact ⟨V, hV, hVne, hs, i, j, hij, commutator_mem_ne_one hK hgK hc⟩

end StepOne

#audit_axioms GroupApproximation.Full.SK02.generalSimple
#audit_axioms GroupApproximation.Full.SK02.generalSimple_printed
#audit_axioms GroupApproximation.Full.SK02.stepOne_movedPointsDense
#audit_axioms GroupApproximation.Full.SK02.stepOne_smallSets
#audit_axioms GroupApproximation.Full.SK02.commutator_mem_ne_one
#audit_axioms GroupApproximation.Full.SK02.stepOne_nonCommutingRoot
#audit_axioms GroupApproximation.Full.SK02.stepOne_commutator

end GroupApproximation.Full.SK02
