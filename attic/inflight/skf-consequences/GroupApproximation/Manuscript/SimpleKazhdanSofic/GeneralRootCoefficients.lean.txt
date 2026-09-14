import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Leavitt.ElementaryNoFiniteQuotients
import GroupApproximation.Leavitt.ElementarySimplicity
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Data.ZMod.Basic

/-!
# The commutation criterion and the coefficients of `c e_V`, for a group action

`simple_kazhdan_sofic_group.tex` at 37551fd93, `\label{sec:proof}`, subsection "Simplicity", tex
l.161–167:

> Indeed, $g$ commutes with $e_{ij}(r)$ exactly when $g_{pi}r=0$ for $p\ne i$, $rg_{jq}=0$ for
> $q\ne j$, and $g_{ii}r=rg_{jj}$. For $c=\sum_\xi c_\xi u_\xi$ and small $V$ we have
> $ce_V=\sum_\xi c_\xi e_{\xi V}u_\xi$ and $e_Vc=\sum_\xi e_Vc_\xi u_\xi$. If $c_\xi\ne0$, it equals
> $1$ on a nonempty clopen set $U$, and a small set $V\subseteq\xi^{-1}U$ gives $ce_V\ne0$, while a
> small set $V\subseteq U$ gives $e_Vc\ne0$.

The ring is `R = LC(Z, F₂) ⋊ Λ`, as `SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ`, with `Λ`
acting on the coefficients through `(ξ • f)(z) = f(ξ⁻¹ • z)` (the printed
`(fu_ξ)(f'u_η) = f(f'∘ξ⁻¹)u_{ξη}`, tex l.135–136).  The element `u_ξ` is `single ξ 1`, and `e_V` is
`single 1 1_V`.

* `commute_elGen_iff`: the commutation criterion, over any ring;
* `coeff_mul_charFn_apply`, `coeff_charFn_mul_apply`: the coefficients of `c e_V` and `e_V c`;
* `exists_forall_coeff_mul_charFn_ne_zero`, `exists_forall_coeff_charFn_mul_ne_zero`: a nonzero
  coefficient survives multiplication by `e_V` for every nonempty clopen `V` in a fixed clopen set.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace General

section Criterion

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The matrix of an element of `EL_ι(R)`. -/
abbrev mat (g : elementaryGroup ι R) : Matrix ι ι R :=
  ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R)

/-- **tex l.161–163**: `g` commutes with `e_{ij}(r)` exactly when `g_{pi} r = 0` for `p ≠ i`,
`r g_{jq} = 0` for `q ≠ j`, and `g_{ii} r = r g_{jj}`. -/
theorem commute_elGen_iff (g : elementaryGroup ι R) {i j : ι} (hij : i ≠ j) (r : R) :
    Commute g (elGen i j hij r) ↔
      (∀ p : ι, p ≠ i → mat g p i * r = 0) ∧ (∀ q : ι, q ≠ j → r * mat g j q = 0) ∧
        mat g i i * r = r * mat g j j := by
  have hmat : Commute g (elGen i j hij r) ↔
      mat g * Matrix.single i j r = Matrix.single i j r * mat g := by
    constructor
    · intro hc
      have hm : mat g * (1 + Matrix.single i j r) = (1 + Matrix.single i j r) * mat g :=
        congrArg (fun z : elementaryGroup ι R => mat z) hc.eq
      rw [mul_add, add_mul, mul_one, one_mul] at hm
      exact add_left_cancel hm
    · intro h
      refine Subtype.ext (Units.ext ?_)
      show mat g * (1 + Matrix.single i j r) = (1 + Matrix.single i j r) * mat g
      rw [mul_add, add_mul, mul_one, one_mul, h]
  rw [hmat]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun q hq => ?_, ?_⟩
    · have hpj := congrFun (congrFun h p) j
      rw [ElementarySimplicity.mul_single_apply, ElementarySimplicity.single_mul_apply,
        if_pos rfl, if_neg hp] at hpj
      exact hpj
    · have hiq := congrFun (congrFun h i) q
      rw [ElementarySimplicity.mul_single_apply, ElementarySimplicity.single_mul_apply,
        if_neg hq, if_pos rfl] at hiq
      exact hiq.symm
    · have hij' := congrFun (congrFun h i) j
      rw [ElementarySimplicity.mul_single_apply, ElementarySimplicity.single_mul_apply,
        if_pos rfl, if_pos rfl] at hij'
      exact hij'
  · rintro ⟨h1, h2, h3⟩
    ext p q
    rw [ElementarySimplicity.mul_single_apply, ElementarySimplicity.single_mul_apply]
    by_cases hq : q = j <;> by_cases hp : p = i
    · subst hq
      subst hp
      rw [if_pos rfl, if_pos rfl]
      exact h3
    · subst hq
      rw [if_pos rfl, if_neg hp]
      exact h1 p hp
    · subst hp
      rw [if_neg hq, if_pos rfl]
      exact (h2 q hq).symm
    · rw [if_neg hq, if_neg hp]

end Criterion

section Coefficients

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z]
  [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]

/-- **tex l.163–164, `c e_V`**: the coefficient at `u_ξ` is `c_ξ e_{ξV}`, pointwise
`c_ξ(y) e_V(ξ⁻¹ • y)`. -/
theorem coeff_mul_charFn_apply
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (c : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ) {V : Set Z} (hV : IsClopen V) (ξ : Λ)
    (y : Z) :
    SkewMonoidAlgebra.coeff (c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))
        ξ y =
      SkewMonoidAlgebra.coeff c ξ y * LocallyConstant.charFn (ZMod 2) hV (ξ⁻¹ • y) := by
  rw [SkewMonoidAlgebra.coeff_mul_single_one, LocallyConstant.mul_apply, hact]

omit [MulAction Λ Z] in
/-- **tex l.164, `e_V c`**: the coefficient at `u_ξ` is `e_V c_ξ`. -/
theorem coeff_charFn_mul_apply (c : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ) {V : Set Z}
    (hV : IsClopen V) (ξ : Λ) (y : Z) :
    SkewMonoidAlgebra.coeff (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c)
        ξ y =
      LocallyConstant.charFn (ZMod 2) hV y * SkewMonoidAlgebra.coeff c ξ y := by
  rw [SkewMonoidAlgebra.coeff_single_one_mul, LocallyConstant.mul_apply]

/-- A nonzero `F₂`-valued locally constant function equals `1` somewhere. -/
theorem exists_eq_one_of_ne_zero {f : LocallyConstant Z (ZMod 2)} (hf : f ≠ 0) :
    ∃ y, f y = 1 := by
  by_contra h
  apply hf
  ext y
  rw [LocallyConstant.zero_apply]
  have hvals : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  exact hvals _ fun h' => h ⟨y, h'⟩

/-- **tex l.165–166, `c e_V`**: if `c_ξ ≠ 0`, it equals `1` on a nonempty clopen set `U`, and every
nonempty clopen `V ⊆ ξ⁻¹U` gives a nonzero coefficient of `c e_V` at `u_ξ`. -/
theorem exists_forall_coeff_mul_charFn_ne_zero [ContinuousConstSMul Λ Z]
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {c : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ} {ξ : Λ}
    (hc : SkewMonoidAlgebra.coeff c ξ ≠ 0) :
    ∃ W : Set Z, IsClopen W ∧ W.Nonempty ∧ ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → V ⊆ W →
      SkewMonoidAlgebra.coeff
        (c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)) ξ ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := exists_eq_one_of_ne_zero hc
  refine ⟨(fun z => ξ • z) ⁻¹' {y | SkewMonoidAlgebra.coeff c ξ y = 1},
    ((SkewMonoidAlgebra.coeff c ξ).isLocallyConstant.isClopen_fiber 1).preimage
      (continuous_const_smul ξ), ⟨ξ⁻¹ • y₀, ?_⟩, fun V hV hne hVW => ?_⟩
  · show SkewMonoidAlgebra.coeff c ξ (ξ • ξ⁻¹ • y₀) = 1
    rw [smul_inv_smul]
    exact hy₀
  · obtain ⟨y, hy⟩ := hne
    intro h0
    have h1 := coeff_mul_charFn_apply hact c hV ξ (ξ • y)
    rw [h0, LocallyConstant.zero_apply, inv_smul_smul, LocallyConstant.coe_charFn,
      Set.indicator_of_mem hy, Pi.one_apply, mul_one] at h1
    have h2 : SkewMonoidAlgebra.coeff c ξ (ξ • y) = 1 := hVW hy
    rw [h2] at h1
    exact absurd h1.symm (by decide)

omit [MulAction Λ Z] in
/-- **tex l.166–167, `e_V c`**: if `c_ξ ≠ 0`, it equals `1` on a nonempty clopen set `U`, and every
nonempty clopen `V ⊆ U` gives a nonzero coefficient of `e_V c` at `u_ξ`. -/
theorem exists_forall_coeff_charFn_mul_ne_zero
    {c : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ} {ξ : Λ}
    (hc : SkewMonoidAlgebra.coeff c ξ ≠ 0) :
    ∃ W : Set Z, IsClopen W ∧ W.Nonempty ∧ ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → V ⊆ W →
      SkewMonoidAlgebra.coeff
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c) ξ ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := exists_eq_one_of_ne_zero hc
  refine ⟨{y | SkewMonoidAlgebra.coeff c ξ y = 1},
    (SkewMonoidAlgebra.coeff c ξ).isLocallyConstant.isClopen_fiber 1, ⟨y₀, hy₀⟩,
    fun V hV hne hVW => ?_⟩
  obtain ⟨y, hy⟩ := hne
  intro h0
  have h1 := coeff_charFn_mul_apply c hV ξ y
  rw [h0, LocallyConstant.zero_apply, LocallyConstant.coe_charFn, Set.indicator_of_mem hy,
    Pi.one_apply, one_mul] at h1
  have h2 : SkewMonoidAlgebra.coeff c ξ y = 1 := hVW hy
  rw [h2] at h1
  exact absurd h1.symm (by decide)

end Coefficients

end General
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.commute_elGen_iff
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.coeff_mul_charFn_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_forall_coeff_mul_charFn_ne_zero
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_forall_coeff_charFn_mul_ne_zero
