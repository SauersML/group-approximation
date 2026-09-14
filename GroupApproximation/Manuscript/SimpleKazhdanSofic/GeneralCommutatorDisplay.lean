import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralCommutatorProducts

/-!
# The display of the commutator products

`simple_kazhdan_sofic_group.tex` at the tip, subsection "Simplicity" (tex l.188–192):

> If $a,b\in B_w$ and $f,f'$ are coefficients as above, then
> \[ fu_a\,e_V\,f'u_b=f\,e_{aV}\,(f'\circ a^{-1})\,u_{ab} \in\{0,\epsilon_{a,b^{-1}}\}, \]
> since $f\circ a$ and $f'$ are constant on $V$.

Over the skew monoid algebra `LC(Z, F_2) ⋊ Λ` of `GeneralCommutatorProducts`, where the action satisfies
`(a • f′) z = f′ (a⁻¹ • z)`, so `a • f′` is the printed `f′∘a⁻¹`:

* `single_mul_charFn_mul_single_eq`: the equality `f u_a e_V f′ u_b = f e_{aV} (a • f′) u_{ab}`;
* `single_mul_charFn_mul_single_eq_zero_or_epsilon`: if `f∘a` and `f′` are constant on `V`, the
  product is `0` or `ε_{a,b⁻¹}`.

`General.single_mul_charFn_mul_single_mem` gives the consequence the proof uses, membership in `A_V`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace General

open scoped Pointwise

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z]
  [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))] [ContinuousConstSMul Λ Z]

/-- **The display, equality** (tex l.189–190): `f u_a e_V f′ u_b = f e_{aV} (f′∘a⁻¹) u_{ab}`, with
`a • f′ = f′∘a⁻¹`. -/
theorem single_mul_charFn_mul_single_eq
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {V : Set Z} (hV : IsClopen V) (a b : Λ) (f f' : LocallyConstant Z (ZMod 2)) :
    SkewMonoidAlgebra.single a f *
          SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) *
        SkewMonoidAlgebra.single b f' =
      SkewMonoidAlgebra.single (a * b)
        (f * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) * a • f') := by
  rw [SkewMonoidAlgebra.single_mul_single, SkewMonoidAlgebra.single_mul_single, mul_one,
    smul_charFn hact]

/-- **The display, dichotomy** (tex l.190–192): if `f∘a` and `f′` are constant on `V`, then
`f u_a e_V f′ u_b ∈ {0, ε_{a,b⁻¹}}`. -/
theorem single_mul_charFn_mul_single_eq_zero_or_epsilon
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    {V : Set Z} (hV : IsClopen V) {a b : Λ} {f f' : LocallyConstant Z (ZMod 2)}
    (hf : ∀ x ∈ V, ∀ y ∈ V, f (a • x) = f (a • y)) (hf' : ∀ x ∈ V, ∀ y ∈ V, f' x = f' y) :
    SkewMonoidAlgebra.single a f *
          SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) *
        SkewMonoidAlgebra.single b f' = 0 ∨
      SkewMonoidAlgebra.single a f *
          SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) *
        SkewMonoidAlgebra.single b f' = epsilon (coeffHom Λ Z) (unitHom Λ Z) hV a b⁻¹ := by
  rw [single_mul_charFn_mul_single_eq hact hV a b f f']
  by_cases hne : V.Nonempty
  swap
  · left
    have hV0 : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have h0 : f * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) * a • f' = 0 := by
      refine LocallyConstant.ext fun z => ?_
      rw [LocallyConstant.mul_apply, LocallyConstant.mul_apply, LocallyConstant.coe_charFn,
        Set.indicator_of_notMem (by rw [hV0, Set.smul_set_empty]; exact Set.notMem_empty z),
        mul_zero, zero_mul, LocallyConstant.zero_apply]
    rw [h0, SkewMonoidAlgebra.single_zero]
  obtain ⟨v₀, hv₀⟩ := hne
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
  rcases hvals (f (a • v₀) * f' v₀) with h0 | h1
  · left
    have hzero : f * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) * a • f' = 0 := by
      refine LocallyConstant.ext fun z => ?_
      rw [hG z, h0, zero_mul, LocallyConstant.zero_apply]
    rw [hzero, SkewMonoidAlgebra.single_zero]
  · right
    have hone : f * LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) * a • f' =
        LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV) := by
      refine LocallyConstant.ext fun z => ?_
      rw [hG z, h1, one_mul]
    rw [hone, ← heps]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.single_mul_charFn_mul_single_eq
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.single_mul_charFn_mul_single_eq_zero_or_epsilon

end General
end SimpleKazhdanSofic
end GroupApproximation
