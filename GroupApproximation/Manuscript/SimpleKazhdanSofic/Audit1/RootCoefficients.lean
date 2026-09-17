import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRoot
import GroupApproximation.Meta.AxiomGuard

/-!
# Audit 1: coefficients of `c e_V` and `e_V c`, and the diagonal of `g`

`simple_kazhdan_sofic_group.tex` (HEAD), proof of simplicity, Step 1.

tex l.259–261:

> If $c_\xi\ne0$, it equals $1$ on a nonempty clopen set $U$, and a small set $V\subseteq\xi^{-1}U$
> gives $ce_V\ne0$, while a small set $V\subseteq U$ gives $e_Vc\ne0$.

tex l.262–265:

> In $g_{ii}e_V=e_Vg_{jj}$ the coefficients at $u_\xi$ with $\xi\ne e$ are supported in the disjoint
> sets $\xi V$ and $V$, so they vanish, and the same argument shows that the corresponding
> coefficients of $g_{ii}$ and $g_{jj}$ vanish.

The ring is the skew monoid algebra `LC(Z, F₂) ⋊ Λ`, with the action on coefficients given by
`(ξ • f)(z) = f(ξ⁻¹ • z)` (`hact`) and a topologically free action (`hfree`).

* `manuscriptSentence_coeffNeZeroGivesProductsNeZero`: for `c_ξ ≠ 0`, the set
  `U = {c_ξ = 1}` is nonempty and clopen. Every nonempty clopen `V ⊆ ξ⁻¹U` has `c e_V ≠ 0`, and
  every nonempty clopen `V ⊆ U` has `e_V c ≠ 0`. For every smallness datum `(D, B, F)`, small sets of
  both kinds exist.
  Route: the coefficient of `c e_V` at `u_ξ` is `c_ξ(y) e_V(ξ⁻¹y)`, which is `1` at `y = ξv` for `v ∈ V`.
  The coefficient of `e_V c` is `e_V(y) c_ξ(y)`, which is `1` at `y ∈ V`. Existence comes from
  `General.exists_isSmall_subset`.
* `manuscriptSentence_diagCoeffsVanish`: if `g ∈ EL_n(R)` commutes with every `e_{ij}(e_V)`,
  `V` small, then for every such `V`:
  * `g_{ii} e_V = e_V g_{jj}`;
  * the coefficient of `g_{ii} e_V` at `u_ξ` is supported in `ξV`, and that of `e_V g_{jj}` in `V`;
  * both vanish for `ξ ≠ e`.

  Moreover the coefficients of `g_{ii}` and `g_{jj}` at `u_ξ` vanish, by
  `General.coeff_diag_eq_zero`, which is the same argument applied to a small `V ⊆ ξ⁻¹U`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Audit1

open scoped Pointwise

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
  [TotallySeparatedSpace Z] [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]

/-- **tex l.259–261.** If `c_ξ ≠ 0`, it equals `1` on the nonempty clopen set `U = {c_ξ = 1}`.
Every nonempty clopen (in particular every small) `V ⊆ ξ⁻¹U` gives `c e_V ≠ 0`, and every nonempty
clopen `V ⊆ U` gives `e_V c ≠ 0`. Small sets of both kinds exist. -/
theorem manuscriptSentence_coeffNeZeroGivesProductsNeZero
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅)
    (c : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ) (ξ : Λ)
    (hc : SkewMonoidAlgebra.coeff c ξ ≠ 0) :
    ∃ U : Set Z, IsClopen U ∧ U.Nonempty ∧ (∀ y ∈ U, SkewMonoidAlgebra.coeff c ξ y = 1) ∧
      (∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → V ⊆ ξ⁻¹ • U →
        c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) ≠ 0) ∧
      (∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → V ⊆ U →
        SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c ≠ 0) ∧
      ∀ (D B : Finset Λ) (F : Finset (LocallyConstant Z (ZMod 2))),
        (∃ (V : Set Z) (hV : IsClopen V), V.Nonempty ∧ V ⊆ ξ⁻¹ • U ∧ General.IsSmall D B F V ∧
          c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) ≠ 0) ∧
        (∃ (V : Set Z) (hV : IsClopen V), V.Nonempty ∧ V ⊆ U ∧ General.IsSmall D B F V ∧
          SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c ≠ 0) := by
  obtain ⟨y₀, hy₀⟩ := General.exists_eq_one_of_ne_zero hc
  have hUc : IsClopen {y : Z | SkewMonoidAlgebra.coeff c ξ y = 1} :=
    (SkewMonoidAlgebra.coeff c ξ).isLocallyConstant.isClopen_fiber 1
  have hUne : ({y : Z | SkewMonoidAlgebra.coeff c ξ y = 1} : Set Z).Nonempty := ⟨y₀, hy₀⟩
  have hleft : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty →
      V ⊆ ξ⁻¹ • {y : Z | SkewMonoidAlgebra.coeff c ξ y = 1} →
      c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) ≠ 0 := by
    intro V hV hne hVU h0
    obtain ⟨y, hy⟩ := hne
    have h3 := Set.mem_smul_set_iff_inv_smul_mem.mp (hVU hy)
    rw [inv_inv] at h3
    have h2 : SkewMonoidAlgebra.coeff c ξ (ξ • y) = 1 := h3
    have h1 := General.coeff_mul_charFn_apply hact c hV ξ (ξ • y)
    rw [inv_smul_smul, LocallyConstant.coe_charFn, Set.indicator_of_mem hy, Pi.one_apply, mul_one,
      h2, h0, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply, LocallyConstant.zero_apply] at h1
    exact absurd h1 (by decide)
  have hright : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty →
      V ⊆ {y : Z | SkewMonoidAlgebra.coeff c ξ y = 1} →
      SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c ≠ 0 := by
    intro V hV hne hVU h0
    obtain ⟨y, hy⟩ := hne
    have h2 : SkewMonoidAlgebra.coeff c ξ y = 1 := hVU hy
    have h1 := General.coeff_charFn_mul_apply c hV ξ y
    rw [LocallyConstant.coe_charFn, Set.indicator_of_mem hy, Pi.one_apply, one_mul, h2, h0,
      SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply, LocallyConstant.zero_apply] at h1
    exact absurd h1 (by decide)
  have hUc' : IsClopen (ξ⁻¹ • {y : Z | SkewMonoidAlgebra.coeff c ξ y = 1}) :=
    ⟨hUc.isClosed.smul ξ⁻¹, hUc.isOpen.smul ξ⁻¹⟩
  have hUne' : (ξ⁻¹ • {y : Z | SkewMonoidAlgebra.coeff c ξ y = 1}).Nonempty := hUne.smul_set
  refine ⟨{y : Z | SkewMonoidAlgebra.coeff c ξ y = 1}, hUc, hUne, fun _ hy => hy, hleft, hright,
    fun D B F => ⟨?_, ?_⟩⟩
  · obtain ⟨V, hV, hne, hVW, hVs⟩ := General.exists_isSmall_subset hfree D B F hUc' hUne'
    exact ⟨V, hV, hne, hVW, hVs, hleft V hV hne hVW⟩
  · obtain ⟨V, hV, hne, hVW, hVs⟩ := General.exists_isSmall_subset hfree D B F hUc hUne
    exact ⟨V, hV, hne, hVW, hVs, hright V hV hne hVW⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_coeffNeZeroGivesProductsNeZero

/-- **tex l.262–265.** Let `g ∈ EL_n(R)` commute with every `e_{ij}(e_V)`, `V` small and nonempty,
with all group elements in the supports of the entries of `g` lying in `D`. Let `i ≠ j` and `ξ ≠ e`.
For every such `V`:
* `g_{ii} e_V = e_V g_{jj}`;
* the coefficient of `g_{ii} e_V` at `u_ξ` is supported in `ξV`;
* that of `e_V g_{jj}` is supported in `V`;
* both therefore vanish.

The corresponding coefficients of `g_{ii}` and `g_{jj}` vanish. -/
theorem manuscriptSentence_diagCoeffsVanish
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {n : ℕ}
    {g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)}
    (hg : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → General.IsSmall D B F V →
      ∀ (i j : Fin n) (hij : i ≠ j),
        Commute g (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))))
    (hD : ∀ (p q : Fin n) (ξ : Λ), ξ ∈ SkewMonoidAlgebra.support (General.mat g p q) → ξ ∈ D)
    {i j : Fin n} (hij : i ≠ j) {ξ : Λ} (hξ : ξ ≠ 1) :
    (∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → General.IsSmall D B F V →
      General.mat g i i * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) =
          SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * General.mat g j j ∧
        (∀ y : Z, SkewMonoidAlgebra.coeff
            (General.mat g i i * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))
              ξ y ≠ 0 → y ∈ ξ • V) ∧
        (∀ y : Z, SkewMonoidAlgebra.coeff
            (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * General.mat g j j)
              ξ y ≠ 0 → y ∈ V) ∧
        SkewMonoidAlgebra.coeff
            (General.mat g i i * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))
              ξ = 0 ∧
        SkewMonoidAlgebra.coeff
            (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * General.mat g j j)
              ξ = 0) ∧
      SkewMonoidAlgebra.coeff (General.mat g i i) ξ = 0 ∧
      SkewMonoidAlgebra.coeff (General.mat g j j) ξ = 0 := by
  refine ⟨fun V hV hne hVs => ?_, General.coeff_diag_eq_zero hact hfree D B F hg hD hij hξ,
    General.coeff_diag_eq_zero hact hfree D B F hg hD (Ne.symm hij) hξ⟩
  have hcomm := ((General.commute_elGen_iff g hij _).mp (hg V hV hne hVs i j hij)).2.2
  have hsupp1 : ∀ y : Z, SkewMonoidAlgebra.coeff
      (General.mat g i i * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))
        ξ y ≠ 0 → y ∈ ξ • V := by
    intro y hy
    by_contra hyV
    have hy' : ξ⁻¹ • y ∉ V := fun h => hyV (Set.mem_smul_set_iff_inv_smul_mem.mpr h)
    apply hy
    rw [General.coeff_mul_charFn_apply hact, LocallyConstant.coe_charFn,
      Set.indicator_of_notMem hy', mul_zero]
  have hsupp2 : ∀ y : Z, SkewMonoidAlgebra.coeff
      (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * General.mat g j j)
        ξ y ≠ 0 → y ∈ V := by
    intro y hy
    by_contra hyV
    apply hy
    rw [General.coeff_charFn_mul_apply, LocallyConstant.coe_charFn, Set.indicator_of_notMem hyV,
      zero_mul]
  have hvan1 : SkewMonoidAlgebra.coeff
      (General.mat g i i * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))
        ξ = 0 := by
    refine LocallyConstant.ext fun y => ?_
    rw [LocallyConstant.zero_apply]
    by_contra hy
    have h1 : y ∈ ξ • V := hsupp1 y hy
    have h2 : y ∈ V := hsupp2 y (by rw [← hcomm]; exact hy)
    by_cases hξD : ξ ∈ D
    · exact Set.disjoint_left.mp (hVs.1 ξ hξD hξ) h2 h1
    · have h0 : SkewMonoidAlgebra.coeff (General.mat g i i) ξ = 0 := by
        by_contra hc
        exact hξD (hD i i ξ (SkewMonoidAlgebra.mem_support_iff.mpr hc))
      apply hy
      rw [General.coeff_mul_charFn_apply hact, h0, LocallyConstant.zero_apply, zero_mul]
  have hvan2 : SkewMonoidAlgebra.coeff
      (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * General.mat g j j)
        ξ = 0 := by
    rw [← hcomm]
    exact hvan1
  exact ⟨hcomm, hsupp1, hsupp2, hvan1, hvan2⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_diagCoeffsVanish

end Audit1
end SimpleKazhdanSofic
end GroupApproximation
