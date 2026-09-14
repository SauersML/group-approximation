import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRootCoefficients
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityStatement
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# The products `f u_a e_V f' u_b` lie in `A_V`, for a group action

`simple_kazhdan_sofic_group.tex` at 37551fd93, `\label{sec:proof}`, subsection "Simplicity", tex
l.188–196:

> Put $k=[g,h]\in K\setminus\{1\}$. If $a,b\in B_w$ and $f,f'$ are coefficients as above, then
> $$fu_a\,e_V\,f'u_b=f\,e_{aV}\,(f'\circ a^{-1})\,u_{ab}\in\{0,\epsilon_{a,b^{-1}}\},$$
> since $f\circ a$ and $f'$ are constant on $V$. The entries of $ghg^{-1}-I_3=g\,e_VE_{ij}\,g^{-1}$
> are sums of such products …

The ring `R = LC(Z, F₂) ⋊ Λ` is `SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ`, with
`(ξ • f)(z) = f(ξ⁻¹ • z)`.  It is a covariant pair in the sense of skf-consequences'
`GeneralSimplicityStatement`: `coeffHom f = f u_e` and `unitHom ξ = u_ξ`.

* `coeffHom`, `unitHom`, `smul_charFn` (`ξ • e_U = e_{ξU}`), `isCovariantPair`;
* `charFn_mem_epsilonSpan`: `e_V = ε_{ee}` lies in `A_V`;
* `single_mul_charFn_mul_single_mem`: the display, `f u_a e_V f'u_b ∈ {0, ε_{a,b⁻¹}} ⊆ A_V`;
* `mul_charFn_mul_mem`: `c e_V c' ∈ A_V` when the `u_ξ` of `c` and the inverses of those of `c'` lie
  in `B`, and the coefficients satisfy the constancy of the display;
* `mul_single_mul_apply`: `(G E_{ij}(a) H)_{pq} = G_{pi} a H_{jq}`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace General

open scoped Pointwise

section Matrices

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- `(G E_{ij}(a) H)_{pq} = G_{pi} a H_{jq}`. -/
theorem mul_single_mul_apply (G H : Matrix ι ι R) (i j : ι) (a : R) (p q : ι) :
    (G * Matrix.single i j a * H) p q = G p i * a * H j q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [ElementarySimplicity.mul_single_apply, if_pos rfl]
  · intro r _ hr
    rw [ElementarySimplicity.mul_single_apply, if_neg hr, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Matrices

variable (Λ Z : Type*) [Group Λ] [TopologicalSpace Z] [MulAction Λ Z]
  [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]

/-- The coefficient embedding `f ↦ f u_e`. -/
noncomputable def coeffHom :
    LocallyConstant Z (ZMod 2) →+* SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ :=
  SkewMonoidAlgebra.singleOneRingHom

/-- The units `u_ξ = single ξ 1`. -/
noncomputable def unitHom : Λ →* (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)ˣ where
  toFun ξ :=
    { val := SkewMonoidAlgebra.single ξ 1
      inv := SkewMonoidAlgebra.single ξ⁻¹ 1
      val_inv := by
        rw [SkewMonoidAlgebra.single_mul_single, mul_inv_cancel, smul_one, mul_one,
          SkewMonoidAlgebra.single_one_one]
      inv_val := by
        rw [SkewMonoidAlgebra.single_mul_single, inv_mul_cancel, smul_one, mul_one,
          SkewMonoidAlgebra.single_one_one] }
  map_one' := Units.ext (by
    show SkewMonoidAlgebra.single (1 : Λ) (1 : LocallyConstant Z (ZMod 2)) = 1
    exact SkewMonoidAlgebra.single_one_one)
  map_mul' ξ η := Units.ext (by
    show SkewMonoidAlgebra.single (ξ * η) (1 : LocallyConstant Z (ZMod 2)) =
      SkewMonoidAlgebra.single ξ 1 * SkewMonoidAlgebra.single η 1
    rw [SkewMonoidAlgebra.single_mul_single, smul_one, mul_one])

variable {Λ Z}

/-- `ξ • e_U = e_{ξU}`. -/
theorem smul_charFn
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    [ContinuousConstSMul Λ Z] (ξ : Λ) {U : Set Z} (hU : IsClopen U) :
    ξ • LocallyConstant.charFn (ZMod 2) hU =
      LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hU) := by
  refine LocallyConstant.ext fun z => ?_
  rw [hact, LocallyConstant.coe_charFn, LocallyConstant.coe_charFn]
  by_cases hz : ξ⁻¹ • z ∈ U
  · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.mpr hz),
      Pi.one_apply]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem fun h => hz (Set.mem_smul_set_iff_inv_smul_mem.mp h)]

/-- **`LC(Z, F₂) ⋊ Λ` is a covariant pair**: `f ↦ f u_e` is injective and `u_ξ e_U = e_{ξU} u_ξ`. -/
theorem isCovariantPair
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    [ContinuousConstSMul Λ Z] : IsCovariantPair (coeffHom Λ Z) (unitHom Λ Z) := by
  refine ⟨SkewMonoidAlgebra.single_injective 1, fun ξ U hU => ?_⟩
  show SkewMonoidAlgebra.single ξ 1 * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hU) =
    SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hU)) *
      SkewMonoidAlgebra.single ξ 1
  simp only [SkewMonoidAlgebra.single_mul_single, mul_one, one_mul, one_smul, smul_charFn hact]

variable [ContinuousConstSMul Λ Z]

/-- **`e_V = ε_{ee}` lies in `A_V`**. -/
theorem charFn_mem_epsilonSpan {B : Finset Λ} (hB1 : (1 : Λ) ∈ B) {V : Set Z} (hV : IsClopen V) :
    SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) ∈
      epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV := by
  have h : epsilon (coeffHom Λ Z) (unitHom Λ Z) hV 1 1 =
      SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) := by
    show SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) (isClopen_smul (1 : Λ) hV)) *
        SkewMonoidAlgebra.single (1 * (1 : Λ)⁻¹) 1 = _
    rw [SkewMonoidAlgebra.single_mul_single, mul_inv_cancel, mul_one, smul_one, mul_one]
    congr 1
    refine LocallyConstant.ext fun z => ?_
    simp only [LocallyConstant.coe_charFn, one_smul]
  rw [← h]
  exact AddSubgroup.subset_closure ⟨1, hB1, 1, hB1, rfl⟩

/-- **The display of tex l.190–194**: if `f ∘ a` and `f'` are constant on `V`, then
`f u_a e_V f' u_b ∈ {0, ε_{a,b⁻¹}} ⊆ A_V`. -/
theorem single_mul_charFn_mul_single_mem
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {B : Finset Λ} {V : Set Z} (hV : IsClopen V) {a b : Λ} (ha : a ∈ B) (hb : b⁻¹ ∈ B)
    {f f' : LocallyConstant Z (ZMod 2)} (hf : ∀ x ∈ V, ∀ y ∈ V, f (a • x) = f (a • y))
    (hf' : ∀ x ∈ V, ∀ y ∈ V, f' x = f' y) :
    SkewMonoidAlgebra.single a f * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) *
        SkewMonoidAlgebra.single b f' ∈ epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV := by
  by_cases hne : V.Nonempty
  swap
  · have hV0 : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have h0 : LocallyConstant.charFn (ZMod 2) hV = 0 := by
      refine LocallyConstant.ext fun z => ?_
      rw [LocallyConstant.coe_charFn,
        Set.indicator_of_notMem (by rw [hV0]; exact Set.notMem_empty z), LocallyConstant.zero_apply]
    rw [h0, SkewMonoidAlgebra.single_zero, mul_zero, zero_mul]
    exact AddSubgroup.zero_mem _
  obtain ⟨v₀, hv₀⟩ := hne
  have hprod : SkewMonoidAlgebra.single a f *
        SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * SkewMonoidAlgebra.single b f' =
      SkewMonoidAlgebra.single (a * b)
        (f * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) * a • f') := by
    rw [SkewMonoidAlgebra.single_mul_single, SkewMonoidAlgebra.single_mul_single, mul_one,
      smul_charFn hact]
  have heps : epsilon (coeffHom Λ Z) (unitHom Λ Z) hV a b⁻¹ =
      SkewMonoidAlgebra.single (a * b) (LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV)) := by
    show SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV)) *
        SkewMonoidAlgebra.single (a * b⁻¹⁻¹) 1 = _
    rw [SkewMonoidAlgebra.single_mul_single, inv_inv, one_mul, one_smul, mul_one]
  have hG : ∀ z : Z, (f * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) * a • f') z =
      f (a • v₀) * f' v₀ * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) z := by
    intro z
    rw [LocallyConstant.mul_apply, LocallyConstant.mul_apply, hact, LocallyConstant.coe_charFn]
    by_cases hz : z ∈ a • V
    · have hz' : a⁻¹ • z ∈ V := Set.mem_smul_set_iff_inv_smul_mem.mp hz
      rw [Set.indicator_of_mem hz, Pi.one_apply, mul_one, mul_one,
        show f z = f (a • v₀) from by rw [← smul_inv_smul a z]; exact hf _ hz' v₀ hv₀,
        hf' _ hz' v₀ hv₀]
    · rw [Set.indicator_of_notMem hz, mul_zero, zero_mul, mul_zero]
  have hvals : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rw [hprod]
  rcases hvals (f (a • v₀) * f' v₀) with h0 | h1
  · have hzero : f * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) * a • f' = 0 := by
      refine LocallyConstant.ext fun z => ?_
      rw [hG z, h0, zero_mul, LocallyConstant.zero_apply]
    rw [hzero, SkewMonoidAlgebra.single_zero]
    exact AddSubgroup.zero_mem _
  · have hone : f * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) * a • f' =
        LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) := by
      refine LocallyConstant.ext fun z => ?_
      rw [hG z, h1, one_mul]
    rw [hone, ← heps]
    exact AddSubgroup.subset_closure ⟨a, ha, b⁻¹, hb, rfl⟩

/-- **tex l.194–196**: `c e_V c'` is a sum of products as in the display, so it lies in `A_V`. -/
theorem mul_charFn_mul_mem
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {B : Finset Λ} {V : Set Z} (hV : IsClopen V)
    {c c' : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ}
    (hc : ∀ a ∈ SkewMonoidAlgebra.support c, a ∈ B ∧
      ∀ x ∈ V, ∀ y ∈ V, SkewMonoidAlgebra.coeff c a (a • x) = SkewMonoidAlgebra.coeff c a (a • y))
    (hc' : ∀ b ∈ SkewMonoidAlgebra.support c', b⁻¹ ∈ B ∧
      ∀ x ∈ V, ∀ y ∈ V, SkewMonoidAlgebra.coeff c' b x = SkewMonoidAlgebra.coeff c' b y) :
    c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c' ∈
      epsilonSpan (coeffHom Λ Z) (unitHom Λ Z) B hV := by
  have hsum : ∀ d : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ,
      d = ∑ a ∈ SkewMonoidAlgebra.support d,
        SkewMonoidAlgebra.single a (SkewMonoidAlgebra.coeff d a) :=
    fun d => (SkewMonoidAlgebra.sum_single d).symm
  rw [hsum c, hsum c', Finset.sum_mul, Finset.sum_mul]
  refine sum_mem fun a ha => ?_
  rw [Finset.mul_sum]
  refine sum_mem fun b hb => ?_
  exact single_mul_charFn_mul_single_mem hact hV (hc a ha).1 (hc' b hb).1 (hc a ha).2 (hc' b hb).2

end General
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.isCovariantPair
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.single_mul_charFn_mul_single_mem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.mul_charFn_mul_mem
