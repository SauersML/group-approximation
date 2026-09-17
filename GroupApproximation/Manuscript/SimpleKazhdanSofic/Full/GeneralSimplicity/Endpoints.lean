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

/-! ### Step 2: the commutator lies in a finite simple group over a tower -/

section StepTwo

open GroupApproximation.SimpleKazhdanSofic (epsilon epsilonSpan TranslatesDisjoint
  GeneralCommutatorWitness)
open GroupApproximation.SimpleKazhdanSofic.General (coeffHom unitHom)

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
  [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]

/-- **Step 2, tex l.278–283**: `ε_ab ε_a'b' = δ_ba' ε_ab'` for `ε_ab = e_{aV} u_{ab⁻¹}`, when the
translates `aV`, `a ∈ B`, are pairwise disjoint. -/
theorem stepTwo_epsilon_mul_epsilon
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    [DecidableEq Λ] {B : Finset Λ} {V : Set Z} (hV : IsClopen V)
    (hdisj : TranslatesDisjoint B V) {a b a' b' : Λ} (hb : b ∈ B) (ha' : a' ∈ B) :
    epsilon (coeffHom Λ Z) (unitHom Λ Z) hV a b * epsilon (coeffHom Λ Z) (unitHom Λ Z) hV a' b' =
      if b = a' then epsilon (coeffHom Λ Z) (unitHom Λ Z) hV a b' else 0 :=
  SimpleKazhdanSofic.General.epsilon_mul_epsilon (SimpleKazhdanSofic.General.isCovariantPair hact)
    hV hdisj hb ha'

/-- **Step 2, tex l.284**: as `V` is nonempty, `ε_ab ≠ 0`. -/
theorem stepTwo_epsilon_ne_zero
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {V : Set Z} (hV : IsClopen V) (hne : V.Nonempty) (a b : Λ) :
    epsilon (coeffHom Λ Z) (unitHom Λ Z) hV a b ≠ 0 :=
  SimpleKazhdanSofic.General.epsilon_ne_zero (SimpleKazhdanSofic.General.isCovariantPair hact)
    hV hne a b

/-- **Step 2, tex l.284–285**: `A_V ≅ M_B(F₂)`: the matrix units `E_ab ↦ ε_ab` extend to an injective
ring homomorphism `M_B(F₂) → R` whose range contains the span `A_V` of the `ε_ab`. -/
theorem stepTwo_ringCopy
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    [DecidableEq Λ] {B : Finset Λ} {V : Set Z} (hV : IsClopen V)
    (hdisj : TranslatesDisjoint B V) (hne : V.Nonempty) :
    ∃ ψ : Matrix B B (ZMod 2) →ₙ+* SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ,
      Function.Injective ψ ∧
      (∀ a b : B, ψ (Matrix.single a b 1) = epsilon (coeffHom Λ Z) (unitHom Λ Z) hV a b) ∧
      ∀ x ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV, ∃ M, ψ M = x := by
  have hcov := SimpleKazhdanSofic.General.isCovariantPair (Λ := Λ) (Z := Z) hact
  exact ⟨SimpleKazhdanSofic.General.epsilonHom hcov hdisj hV,
    SimpleKazhdanSofic.General.epsilonHom_injective hcov hdisj hV hne,
    SimpleKazhdanSofic.General.epsilonHom_single hcov hdisj hV,
    fun _ hx => SimpleKazhdanSofic.General.mem_range_epsilonHom_of_mem_epsilonSpan hcov hdisj hV hx⟩

/-- **Step 2, tex l.280–281**: `A_V` is closed under products. -/
theorem stepTwo_epsilonSpan_mul_mem
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    [DecidableEq Λ] {B : Finset Λ} {V : Set Z} (hV : IsClopen V) (hdisj : TranslatesDisjoint B V)
    {x y : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ}
    (hx : x ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV)
    (hy : y ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV) :
    x * y ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV :=
  SimpleKazhdanSofic.General.epsilonSpan_mul_mem (SimpleKazhdanSofic.General.isCovariantPair hact)
    hV hdisj hx hy

/-- **Step 2, tex l.285–289**: `y ↦ (1 - 1_V) I + y` embeds `GL_ι(A_V) ≅ GL_{ι × B}(F₂)` in
`GL_ι(R)`; its image `H_V` lies in `G = EL_ι(R)`, the transvection between `(p, a)` and `(q, b)`,
`p ≠ q`, maps to `e_pq(ε_ab)`, and (tex l.300–302) every `k` with `k - I` and `k⁻¹ - I` in
`M_ι(A_V)` lies in `H_V`. -/
theorem stepTwo_towerCopy
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    [DecidableEq Λ] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] {B : Finset Λ}
    {V : Set Z} (hV : IsClopen V) (hdisj : TranslatesDisjoint B V) (hne : V.Nonempty) :
    ∃ H : (Matrix (ι × B) (ι × B) (ZMod 2))ˣ →*
        (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ,
      Function.Injective H ∧
      (∀ x, H x ∈ elementaryGroup ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) ∧
      (∀ (p q : ι) (hpq : p ≠ q) (a b : B) (h : ((p, a) : ι × B) ≠ (q, b)),
        H (elementaryUnit (p, a) (q, b) h (1 : ZMod 2)) =
          elementaryUnit p q hpq (epsilon (coeffHom Λ Z) (unitHom Λ Z) hV a b)) ∧
      ∀ g : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ,
        (∀ p q, ((g : Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1) p q ∈
          epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV) →
        (∀ p q, (((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) :
            Matrix ι ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)) - 1) p q ∈
          epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV) →
        ∃ x, H x = g := by
  have hcov := SimpleKazhdanSofic.General.isCovariantPair (Λ := Λ) (Z := Z) hact
  exact ⟨SimpleKazhdanSofic.General.copyGL hcov ι hdisj hV,
    SimpleKazhdanSofic.General.copyGL_injective hcov hdisj hV hne,
    SimpleKazhdanSofic.General.copyGL_mem_elementaryGroup hcov hdisj hV,
    fun _ _ hpq a b h => SimpleKazhdanSofic.General.copyGL_transvection hcov hdisj hV hpq a b h,
    fun g hg hginv => SimpleKazhdanSofic.General.exists_copyGL_eq hcov hdisj hV hne g hg hginv⟩

/-- **Step 2, tex l.303–305**: `GL_d(F₂) = PSL_d(F₂)` is simple for `d ≥ 3`. -/
theorem stepTwo_glSimple (κ : Type*) [Fintype κ] [DecidableEq κ] (hcard : 3 ≤ Fintype.card κ) :
    IsSimpleGroup (Matrix κ κ (ZMod 2))ˣ :=
  FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo κ hcard

/-- **Step 2, the display of tex l.291–296**: if every `a` in the support of `c` lies in `B` with
`c_a ∘ a` constant on `V`, and every `b` in the support of `c'` has `b⁻¹ ∈ B` with `c'_b` constant on
`V`, then `c e_V c'` is a sum of products `f u_a e_V f' u_b ∈ {0, ε_{a,b⁻¹}}`, so it lies in `A_V`. -/
theorem stepTwo_mul_charFn_mul_mem
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {B : Finset Λ} {V : Set Z} (hV : IsClopen V)
    {c c' : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ}
    (hc : ∀ a ∈ SkewMonoidAlgebra.support c, a ∈ B ∧
      ∀ x ∈ V, ∀ y ∈ V, SkewMonoidAlgebra.coeff c a (a • x) = SkewMonoidAlgebra.coeff c a (a • y))
    (hc' : ∀ b ∈ SkewMonoidAlgebra.support c', b⁻¹ ∈ B ∧
      ∀ x ∈ V, ∀ y ∈ V, SkewMonoidAlgebra.coeff c' b x = SkewMonoidAlgebra.coeff c' b y) :
    c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c' ∈
      epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV :=
  SimpleKazhdanSofic.General.mul_charFn_mul_mem hact hV hc hc'

/-- **Steps 1–2, as printed** (tex l.243–306): for a topologically free action on a totally separated
space and `n ≥ 2`, every nontrivial normal subgroup `K` of `EL_n(R)` contains `x ≠ 1` such that, for
some nonempty clopen `V` and finite `B ∋ e` with pairwise disjoint translates `aV`, `a ∈ B`, the
matrices `x - I` and `x⁻¹ - I` lie in `M_n(A_V)`. -/
theorem stepTwo_commutatorWitness [TotallySeparatedSpace Z]
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {n : ℕ} (hn : 2 ≤ n) :
    GeneralCommutatorWitness (coeffHom Λ Z) (unitHom Λ Z) n :=
  SimpleKazhdanSofic.General.generalCommutatorWitness hact hfree hn

end StepTwo

/-! ### Step 3: `K` contains every elementary matrix -/

section StepThree

open GroupApproximation.SimpleKazhdanSofic.General (coeffHom unitHom)

/-- **Step 3, tex l.308–312**: `J = {r ∈ R : e_pq(r) ∈ K for all p ≠ q}` is a two-sided ideal. -/
theorem stepThree_levelIdeal {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (hcard : 3 ≤ Fintype.card ι) (K : Subgroup (elementaryGroup ι R)) [K.Normal] (r : R) :
    r ∈ levelIdeal hcard K ↔ ∀ (p q : ι) (hpq : p ≠ q), elGen p q hpq r ∈ K :=
  mem_levelIdeal hcard K r

/-- **Step 3, tex l.315**: if `1 ∈ J`, then `J = R` and `K = G`. -/
theorem stepThree_eq_top_of_one_mem {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (hcard : 3 ≤ Fintype.card ι) (K : Subgroup (elementaryGroup ι R)) [K.Normal]
    (h1 : (1 : R) ∈ levelIdeal hcard K) : K = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro y
  have hy := elementaryGroup_hom_eq_one_of_gens (QuotientGroup.mk' K)
    (fun l k hlk d => by
      have hd := TwoSidedIdeal.mul_mem_left _ d 1 h1
      rw [mul_one] at hd
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (mem_levelIdeal hcard K d).mp hd l k hlk) y
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]

/-- **Step 3, tex l.313–314**: by minimality and compactness, finitely many translates `ξV` of a
nonempty open set `V` cover `C`. -/
theorem stepThree_finiteCover [CompactSpace Z] [MulAction.IsMinimal Λ Z] {V : Set Z}
    (hV : IsOpen V) (hne : V.Nonempty) : ∃ s : Finset Λ, ∀ z : Z, ∃ ξ ∈ s, z ∈ ξ • V :=
  SimpleKazhdanSofic.General.exists_finset_smul_cover hV hne

variable [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]

/-- **Step 3, tex l.312–313**: if `e_V ∈ J`, then every `e_{ξV} = u_ξ e_V u_ξ⁻¹` lies in `J`. -/
theorem stepThree_charFn_smul_mem
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hcard : 3 ≤ Fintype.card ι)
    (K : Subgroup (elementaryGroup ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) [K.Normal]
    {V : Set Z} (hV : IsClopen V)
    (hmem : coeffHom Λ Z (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard K) (ξ : Λ) :
    coeffHom Λ Z (LocallyConstant.charFn (ZMod 2) (SimpleKazhdanSofic.isClopen_smul ξ hV)) ∈
      levelIdeal hcard K := by
  rw [← SimpleKazhdanSofic.General.unit_mul_charFn_mul_inv
    (SimpleKazhdanSofic.General.isCovariantPair hact) ξ hV]
  exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hmem)

/-- **Step 3, tex l.312–315**: if `e_V ∈ J` and the translates `ξV`, `ξ ∈ s`, cover `C`, then
`1 = 1 - ∏ᵢ (1 - e_{ξᵢV}) ∈ J`. -/
theorem stepThree_one_mem
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hcard : 3 ≤ Fintype.card ι) {V : Set Z}
    (hV : IsClopen V) (s : Finset Λ) (hs : ∀ z : Z, ∃ ξ ∈ s, z ∈ ξ • V)
    (K : Subgroup (elementaryGroup ι (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) [K.Normal]
    (hmem : coeffHom Λ Z (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard K) :
    (1 : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ) ∈ levelIdeal hcard K :=
  SimpleKazhdanSofic.General.one_mem_levelIdeal_of_smul_cover
    (SimpleKazhdanSofic.General.isCovariantPair hact) hcard hV s hs K hmem

/-- **Steps 1–3, as printed** (tex l.241–315): for a minimal topologically free action on a nonempty
compact totally separated space and `n ≥ 3`, every nontrivial normal subgroup `K` of `EL_n(R)` is
`EL_n(R)`. -/
theorem stepThree_normalSubgroupEqTop [TotallySeparatedSpace Z] [CompactSpace Z]
    [MulAction.IsMinimal Λ Z]
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {n : ℕ} (hn : 3 ≤ n)
    (K : Subgroup (elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)))
    (hK : K.Normal) (hne : K ≠ ⊥) : K = ⊤ :=
  SimpleKazhdanSofic.General.eq_top_of_generalCommutatorWitness
    (SimpleKazhdanSofic.General.isCovariantPair hact) hn
    (SimpleKazhdanSofic.General.generalCommutatorWitness hact hfree (by omega))
    (fun _ hV hne' => SimpleKazhdanSofic.General.exists_finset_smul_cover hV.isOpen hne') K hK hne

end StepThree

#audit_axioms GroupApproximation.Full.SK02.generalSimple
#audit_axioms GroupApproximation.Full.SK02.generalSimple_printed
#audit_axioms GroupApproximation.Full.SK02.stepOne_movedPointsDense
#audit_axioms GroupApproximation.Full.SK02.stepOne_smallSets
#audit_axioms GroupApproximation.Full.SK02.commutator_mem_ne_one
#audit_axioms GroupApproximation.Full.SK02.stepOne_nonCommutingRoot
#audit_axioms GroupApproximation.Full.SK02.stepOne_commutator
#audit_axioms GroupApproximation.Full.SK02.stepTwo_epsilon_mul_epsilon
#audit_axioms GroupApproximation.Full.SK02.stepTwo_epsilon_ne_zero
#audit_axioms GroupApproximation.Full.SK02.stepTwo_ringCopy
#audit_axioms GroupApproximation.Full.SK02.stepTwo_epsilonSpan_mul_mem
#audit_axioms GroupApproximation.Full.SK02.stepTwo_towerCopy
#audit_axioms GroupApproximation.Full.SK02.stepTwo_glSimple
#audit_axioms GroupApproximation.Full.SK02.stepTwo_mul_charFn_mul_mem
#audit_axioms GroupApproximation.Full.SK02.stepTwo_commutatorWitness
#audit_axioms GroupApproximation.Full.SK02.stepThree_levelIdeal
#audit_axioms GroupApproximation.Full.SK02.stepThree_eq_top_of_one_mem
#audit_axioms GroupApproximation.Full.SK02.stepThree_finiteCover
#audit_axioms GroupApproximation.Full.SK02.stepThree_charFn_smul_mem
#audit_axioms GroupApproximation.Full.SK02.stepThree_one_mem
#audit_axioms GroupApproximation.Full.SK02.stepThree_normalSubgroupEqTop

end GroupApproximation.Full.SK02
