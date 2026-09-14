import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimplicityNonCommutingRoot
import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Meta.AxiomGuard

/-!
# When a root commutes with `g`, and the coefficients of `c e_V` and `e_V c`

`simple_kazhdan_sofic_group.tex` at 9047d0d3c, subsection "Simplicity", tex l.198–203:

> Indeed, $g$ commutes with $e_{ij}(r)$ exactly when $g_{pi}r=0$ for $p\ne i$, $rg_{jq}=0$ for
> $q\ne j$, and $g_{ii}r=rg_{jj}$. For $c=\sum_tc_tu^t$ and small $V$ we have
> $ce_V=\sum_tc_te_{T^tV}u^t$ and $e_Vc=\sum_te_Vc_tu^t$. If $c_t\ne0$, it equals $1$ on a nonempty
> clopen set $U$, and a small set $V\subseteq T^{-t}U$ gives $ce_V\ne0$, while a small set
> $V\subseteq U$ gives $e_Vc\ne0$.

* `commute_elGen_iff`: the printed criterion, for any finite index type and any ring;
* `coeff_mul_charFn_apply`, `coeff_charFn_mul_apply`: the coefficients of `c e_V` and `e_V c`,
  pointwise (`e_V ∘ T^{-t} = e_{T^tV}`);
* `exists_eq_one_of_ne_zero`: a nonzero `F₂`-valued coefficient equals `1` somewhere;
* `exists_forall_coeff_mul_charFn_ne_zero`, `exists_forall_coeff_charFn_mul_ne_zero`: for `c_t ≠ 0`
  there is a nonempty clopen set (`T^{-t}U`, resp. `U`) such that every nonempty clopen `V` inside it
  gives a nonzero coefficient of `c e_V`, resp. `e_V c`, at `u^t`.
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic

open GroupApproximation.Pestov91 GroupApproximation.ClopenCrossedProduct
open Multiplicative (ofAdd toAdd)

section Criterion

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **tex l.198–199**: `g` commutes with `e_{ij}(r)` exactly when `g_{pi} r = 0` for `p ≠ i`,
`r g_{jq} = 0` for `q ≠ j`, and `g_{ii} r = r g_{jj}`. -/
theorem commute_elGen_iff (g : elementaryGroup ι R) {i j : ι} (hij : i ≠ j) (r : R) :
    Commute g (elGen i j hij r) ↔
      (∀ p : ι, p ≠ i → ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) p i * r = 0) ∧
        (∀ q : ι, q ≠ j → r * ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) j q = 0) ∧
        ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) i i * r =
          r * ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j := by
  have hmat : Commute g (elGen i j hij r) ↔
      ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) * Matrix.single i j r =
        Matrix.single i j r * ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) := by
    constructor
    · intro hc
      exact (single_mul_eq_mul_single_of_commute_elGen hij hc).symm
    · intro h
      refine Subtype.ext (Units.ext ?_)
      show ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) * (1 + Matrix.single i j r) =
        (1 + Matrix.single i j r) * ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R)
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

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

/-- **The coefficients of `c e_V`** (tex l.200): the coefficient at `u^t` is `c_t e_{T^tV}`,
evaluated pointwise as `c_t(y) e_V(T^{-t} y)`. -/
theorem coeff_mul_charFn_apply (c : ClopenCrossedProduct T (ZMod 2)) {V : Set X}
    (hV : IsClopen V) (g : Multiplicative ℤ) (y : X) :
    (ClopenCoeff.of T (ZMod 2)).symm
        (SkewMonoidAlgebra.coeff (c * coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV)) g) y =
      (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g) y *
        LocallyConstant.charFn (ZMod 2) hV ((T ^ (-toAdd g)) y) := by
  rw [coeff_apply, Pestov91.CrossedProduct.C_apply, SkewMonoidAlgebra.coeff_mul_single_one,
    map_mul, LocallyConstant.mul_apply, of_symm_smul_apply, RingEquiv.symm_apply_apply]

/-- **The coefficients of `e_V c`** (tex l.201): the coefficient at `u^t` is `e_V c_t`. -/
theorem coeff_charFn_mul_apply (c : ClopenCrossedProduct T (ZMod 2)) {V : Set X}
    (hV : IsClopen V) (g : Multiplicative ℤ) (y : X) :
    (ClopenCoeff.of T (ZMod 2)).symm
        (SkewMonoidAlgebra.coeff (coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV) * c) g) y =
      LocallyConstant.charFn (ZMod 2) hV y *
        (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g) y := by
  rw [coeff_apply, Pestov91.CrossedProduct.C_apply, SkewMonoidAlgebra.coeff_single_one_mul,
    map_mul, LocallyConstant.mul_apply, RingEquiv.symm_apply_apply]

/-- A nonzero `F₂`-valued locally constant function equals `1` somewhere. -/
theorem exists_eq_one_of_ne_zero {f : LocallyConstant X (ZMod 2)} (hf : f ≠ 0) : ∃ y, f y = 1 := by
  by_contra h
  apply hf
  ext y
  rw [LocallyConstant.zero_apply]
  have hvals : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  exact hvals _ fun h' => h ⟨y, h'⟩

theorem of_symm_ne_zero {c : ClopenCoeff T (ZMod 2)} (hc : c ≠ 0) :
    (ClopenCoeff.of T (ZMod 2)).symm c ≠ 0 := fun h =>
  hc (by rw [← (ClopenCoeff.of T (ZMod 2)).apply_symm_apply c, h, map_zero])

/-- **tex l.201–203, right side**: if `c_t ≠ 0`, there is a nonempty clopen set `T^{-t}U` such that
every nonempty clopen `V ⊆ T^{-t}U` gives a nonzero coefficient of `c e_V` at `u^t`. -/
theorem exists_forall_coeff_mul_charFn_ne_zero {c : ClopenCrossedProduct T (ZMod 2)}
    {g : Multiplicative ℤ} (hc : SkewMonoidAlgebra.coeff c g ≠ 0) :
    ∃ W : Set X, IsClopen W ∧ W.Nonempty ∧ ∀ (V : Set X) (hV : IsClopen V), V.Nonempty → V ⊆ W →
      SkewMonoidAlgebra.coeff (c * coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV)) g ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := exists_eq_one_of_ne_zero (of_symm_ne_zero T hc)
  refine ⟨⇑(T ^ toAdd g) ⁻¹'
      {y | (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g) y = 1},
    (((ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g)).isLocallyConstant.isClopen_fiber
      1).preimage (T ^ toAdd g).continuous, ⟨(T ^ (-toAdd g)) y₀, ?_⟩, fun V hV hne hVW => ?_⟩
  · show (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g)
        ((T ^ toAdd g) ((T ^ (-toAdd g)) y₀)) = 1
    rw [← Homeomorph.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Homeomorph.one_apply]
    exact hy₀
  · obtain ⟨y, hy⟩ := hne
    intro h0
    have h1 := coeff_mul_charFn_apply T c hV g ((T ^ toAdd g) y)
    rw [h0, map_zero, LocallyConstant.zero_apply, ← Homeomorph.mul_apply, ← zpow_add,
      neg_add_cancel, zpow_zero, Homeomorph.one_apply, LocallyConstant.coe_charFn,
      Set.indicator_of_mem hy, Pi.one_apply, mul_one] at h1
    have h2 : (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g) ((T ^ toAdd g) y) = 1 :=
      hVW hy
    rw [h2] at h1
    exact absurd h1.symm (by decide)

/-- **tex l.201–203, left side**: if `c_t ≠ 0`, there is a nonempty clopen set `U` such that every
nonempty clopen `V ⊆ U` gives a nonzero coefficient of `e_V c` at `u^t`. -/
theorem exists_forall_coeff_charFn_mul_ne_zero {c : ClopenCrossedProduct T (ZMod 2)}
    {g : Multiplicative ℤ} (hc : SkewMonoidAlgebra.coeff c g ≠ 0) :
    ∃ W : Set X, IsClopen W ∧ W.Nonempty ∧ ∀ (V : Set X) (hV : IsClopen V), V.Nonempty → V ⊆ W →
      SkewMonoidAlgebra.coeff (coeff T (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV) * c) g ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := exists_eq_one_of_ne_zero (of_symm_ne_zero T hc)
  refine ⟨{y | (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g) y = 1},
    ((ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g)).isLocallyConstant.isClopen_fiber
      1, ⟨y₀, hy₀⟩, fun V hV hne hVW => ?_⟩
  obtain ⟨y, hy⟩ := hne
  intro h0
  have h1 := coeff_charFn_mul_apply T c hV g y
  rw [h0, map_zero, LocallyConstant.zero_apply, LocallyConstant.coe_charFn,
    Set.indicator_of_mem hy, Pi.one_apply, one_mul] at h1
  have h2 : (ClopenCoeff.of T (ZMod 2)).symm (SkewMonoidAlgebra.coeff c g) y = 1 := hVW hy
  rw [h2] at h1
  exact absurd h1.symm (by decide)

end Coefficients

end SimpleKazhdanSofic
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.commute_elGen_iff
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.coeff_mul_charFn_apply
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.coeff_charFn_mul_apply
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.exists_forall_coeff_mul_charFn_ne_zero
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.exists_forall_coeff_charFn_mul_ne_zero
