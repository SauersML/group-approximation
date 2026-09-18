import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSmallSets
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRootCoefficients

/-!
# A root over a small set that does not commute with `g`, for a group action

`simple_kazhdan_sofic_group.tex` at 37551fd93, `\label{sec:proof}`, subsection "Simplicity", tex
l.161 and l.167–174:

> Some $h=e_{ij}(e_V)$ with $V$ small does not commute with $g$. … So if $g$ commutes with every
> such $h$, then $g$ is diagonal. In $g_{ii}e_V=e_Vg_{jj}$ the coefficients at $u_\xi$ with
> $\xi\ne e$ are supported in the disjoint sets $\xi V$ and $V$, so they vanish, and the same
> argument shows that the corresponding coefficients of $g_{ii}$ and $g_{jj}$ vanish. The constant
> coefficients agree on every small $V$, so they agree everywhere. So $g=cI_3$ with
> $c\in\LC(Z,\F_2)$, and comparing constant coefficients in $cc^{-1}=1$ gives $c=1$ and $g=1$.

The proof is written for `EL_n`, `n ≥ 2`; the note needs `n ≥ 3` (tex l.131).  `D` is the printed
`B_{2w}` and contains every `ξ` occurring in the entries of `g`.

* `eq_zero_of_forall_mul_charFn`, `eq_zero_of_forall_charFn_mul`: "as above";
* `offDiag_eq_zero`: `g` is diagonal;
* `coeff_diag_eq_zero`: the coefficients of the diagonal entries at `u_ξ`, `ξ ≠ e`, vanish;
* `coeff_one_diag_eq`: the constant coefficients agree;
* `eq_one_of_commute_elGen_small`: `g = 1`;
* `exists_isSmall_not_commute_elGen` and the closed endpoint `printedGeneralNonCommutingRoot`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace General

open scoped Pointwise

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
  [TotallySeparatedSpace Z] [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]

/-- **"As above"** (tex l.167): `c e_V = 0` for every small nonempty clopen `V` forces `c = 0`. -/
theorem eq_zero_of_forall_mul_charFn
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {c : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ}
    (hc : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsSmall D B F V →
      c * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) = 0) : c = 0 := by
  refine SkewMonoidAlgebra.ext fun ξ => ?_
  rw [SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hξ
  obtain ⟨W, hWc, hWne, hW⟩ := exists_forall_coeff_mul_charFn_ne_zero hact hξ
  obtain ⟨V, hVc, hVne, hVW, hVs⟩ := exists_isSmall_subset hfree D B F hWc hWne
  exact hW V hVc hVne hVW
    (by rw [hc V hVc hVne hVs, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply])

/-- **"As above"** (tex l.167): `e_V c = 0` for every small nonempty clopen `V` forces `c = 0`. -/
theorem eq_zero_of_forall_charFn_mul
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {c : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ}
    (hc : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsSmall D B F V →
      SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV) * c = 0) : c = 0 := by
  refine SkewMonoidAlgebra.ext fun ξ => ?_
  rw [SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hξ
  obtain ⟨W, hWc, hWne, hW⟩ := exists_forall_coeff_charFn_mul_ne_zero hξ
  obtain ⟨V, hVc, hVne, hVW, hVs⟩ := exists_isSmall_subset hfree D B F hWc hWne
  exact hW V hVc hVne hVW
    (by rw [hc V hVc hVne hVs, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply])

/-- **tex l.167–168**: if `g` commutes with every `e_{ij}(e_V)`, `V` small, then `g` is diagonal. -/
theorem offDiag_eq_zero
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {n : ℕ} (hn : 2 ≤ n)
    {g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)}
    (hg : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsSmall D B F V →
      ∀ (i j : Fin n) (hij : i ≠ j),
        Commute g (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))))
    {p i : Fin n} (hpi : p ≠ i) : mat g p i = 0 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  exact eq_zero_of_forall_mul_charFn hact hfree D B F fun V hV hne hs =>
    ((commute_elGen_iff g (Ne.symm hji) _).mp (hg V hV hne hs i j (Ne.symm hji))).1 p hpi

/-- **tex l.168–171**: in `g_{ii} e_V = e_V g_{jj}` the coefficients at `u_ξ`, `ξ ≠ e`, are supported
in the disjoint sets `ξV` and `V`, so the coefficients of `g_{ii}` at these `u_ξ` vanish. -/
theorem coeff_diag_eq_zero
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {n : ℕ}
    {g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)}
    (hg : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsSmall D B F V →
      ∀ (i j : Fin n) (hij : i ≠ j),
        Commute g (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))))
    (hD : ∀ (p q : Fin n) (ξ : Λ), ξ ∈ SkewMonoidAlgebra.support (mat g p q) → ξ ∈ D)
    {i j : Fin n} (hij : i ≠ j) {ξ : Λ} (hξ : ξ ≠ 1) :
    SkewMonoidAlgebra.coeff (mat g i i) ξ = 0 := by
  by_contra hc
  have hξD : ξ ∈ D := hD i i ξ (SkewMonoidAlgebra.mem_support_iff.mpr hc)
  obtain ⟨W, hWc, hWne, hW⟩ := exists_forall_coeff_mul_charFn_ne_zero hact hc
  obtain ⟨V, hVc, hVne, hVW, hVs⟩ := exists_isSmall_subset hfree D B F hWc hWne
  refine hW V hVc hVne hVW ?_
  have hcomm := ((commute_elGen_iff g hij _).mp (hg V hVc hVne hVs i j hij)).2.2
  refine LocallyConstant.ext fun y => ?_
  rw [LocallyConstant.zero_apply]
  by_cases hy : ξ⁻¹ • y ∈ V
  · have hyV : y ∉ V := fun hyV' =>
      (Set.disjoint_left.mp (hVs.1 ξ hξD hξ)) hyV' (Set.mem_smul_set_iff_inv_smul_mem.mpr hy)
    rw [hcomm, coeff_charFn_mul_apply, LocallyConstant.coe_charFn, Set.indicator_of_notMem hyV,
      zero_mul]
  · rw [coeff_mul_charFn_apply hact, LocallyConstant.coe_charFn, Set.indicator_of_notMem hy,
      mul_zero]

/-- **tex l.171–172**: the constant coefficients of `g_{ii}` and `g_{jj}` agree on every small `V`,
so they agree everywhere. -/
theorem coeff_one_diag_eq
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {n : ℕ}
    {g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)}
    (hg : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsSmall D B F V →
      ∀ (i j : Fin n) (hij : i ≠ j),
        Commute g (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))))
    {i j : Fin n} (hij : i ≠ j) :
    SkewMonoidAlgebra.coeff (mat g i i) 1 = SkewMonoidAlgebra.coeff (mat g j j) 1 := by
  by_contra hne
  have hA : IsClopen {y : Z | (SkewMonoidAlgebra.coeff (mat g i i) 1 -
      SkewMonoidAlgebra.coeff (mat g j j) 1) y = 0}ᶜ :=
    ((SkewMonoidAlgebra.coeff (mat g i i) 1 -
      SkewMonoidAlgebra.coeff (mat g j j) 1).isLocallyConstant.isClopen_fiber 0).compl
  have hAne : ({y : Z | (SkewMonoidAlgebra.coeff (mat g i i) 1 -
      SkewMonoidAlgebra.coeff (mat g j j) 1) y = 0}ᶜ).Nonempty := by
    by_contra h0
    apply hne
    refine LocallyConstant.ext fun y => ?_
    by_contra hy
    have hyA : y ∈ {y : Z | (SkewMonoidAlgebra.coeff (mat g i i) 1 -
        SkewMonoidAlgebra.coeff (mat g j j) 1) y = 0}ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, LocallyConstant.sub_apply, sub_eq_zero]
      exact hy
    exact h0 ⟨y, hyA⟩
  obtain ⟨V, hVc, ⟨y, hy⟩, hVA, hVs⟩ := exists_isSmall_subset hfree D B F hA hAne
  have hcomm := ((commute_elGen_iff g hij _).mp (hg V hVc ⟨y, hy⟩ hVs i j hij)).2.2
  have h1 : SkewMonoidAlgebra.coeff
        (mat g i i * SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hVc)) 1 y =
      SkewMonoidAlgebra.coeff
        (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hVc) * mat g j j) 1 y := by
    rw [hcomm]
  rw [coeff_mul_charFn_apply hact, coeff_charFn_mul_apply, inv_one, one_smul,
    LocallyConstant.coe_charFn, Set.indicator_of_mem hy, Pi.one_apply, mul_one, one_mul] at h1
  exact hVA hy (by simp only [Set.mem_setOf_eq, LocallyConstant.sub_apply, h1, sub_self])

/-- **tex l.161–174**: if `g ∈ EL_n(R)` commutes with `e_{ij}(e_V)` for every small nonempty clopen
`V` and all `i ≠ j`, and `D` contains every `ξ` occurring in the entries of `g`, then `g = 1`. -/
theorem eq_one_of_commute_elGen_small
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {n : ℕ} (hn : 2 ≤ n)
    {g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)}
    (hg : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsSmall D B F V →
      ∀ (i j : Fin n) (hij : i ≠ j),
        Commute g (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))))
    (hD : ∀ (p q : Fin n) (ξ : Λ), ξ ∈ SkewMonoidAlgebra.support (mat g p q) → ξ ∈ D) :
    g = 1 := by
  classical
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hzero : ∀ (p : Fin n) {ξ : Λ}, ξ ≠ 1 → SkewMonoidAlgebra.coeff (mat g p p) ξ = 0 := by
    intro p ξ hξ
    obtain ⟨j, hjp⟩ := exists_ne p
    exact coeff_diag_eq_zero hact hfree D B F hg hD (Ne.symm hjp) hξ
  have hdiag : ∀ p : Fin n, mat g p p = mat g i₀ i₀ := by
    intro p
    refine SkewMonoidAlgebra.ext fun ξ => ?_
    by_cases hξ : ξ = 1
    · subst hξ
      by_cases hp : p = i₀
      · rw [hp]
      · exact coeff_one_diag_eq hact hfree D B F hg hp
    · rw [hzero p hξ, hzero i₀ hξ]
  have hscalar : mat g = Matrix.scalar (Fin n) (mat g i₀ i₀) := by
    refine Matrix.ext fun p q ↦ ?_
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hpq : p = q
    · rw [if_pos hpq, hpq, hdiag q]
    · rw [if_neg hpq, offDiag_eq_zero hact hfree D B F hn hg hpq]
  have hc0 : mat g i₀ i₀ = SkewMonoidAlgebra.single (1 : Λ) (SkewMonoidAlgebra.coeff (mat g i₀ i₀) 1) := by
    refine SkewMonoidAlgebra.ext fun ξ => ?_
    rw [SkewMonoidAlgebra.coeff_single_apply]
    by_cases hξ : ξ = 1
    · rw [if_pos hξ.symm, hξ]
    · rw [if_neg (Ne.symm hξ), hzero i₀ hξ]
  have hinv : mat g i₀ i₀ * mat g⁻¹ i₀ i₀ = 1 := by
    have h1 : mat g * mat g⁻¹ = 1 := by
      simp only [mat, Subgroup.coe_inv, Units.mul_inv]
    rw [hscalar] at h1
    simpa [Matrix.scalar_apply] using congrFun (congrFun h1 i₀) i₀
  have hf1 : SkewMonoidAlgebra.coeff (mat g i₀ i₀) 1 = 1 := by
    have h2 : SkewMonoidAlgebra.coeff (mat g i₀ i₀ * mat g⁻¹ i₀ i₀) 1 =
        SkewMonoidAlgebra.coeff (1 : SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ) 1 := by
      rw [hinv]
    rw [hc0, SkewMonoidAlgebra.coeff_single_one_mul, SkewMonoidAlgebra.coeff_one,
      Finsupp.single_eq_same] at h2
    refine LocallyConstant.ext fun y => ?_
    have hy := LocallyConstant.congr_fun h2 y
    rw [LocallyConstant.mul_apply, LocallyConstant.one_apply] at hy
    rw [LocallyConstant.one_apply]
    have hvals : ∀ a b : ZMod 2, a * b = 1 → a = 1 := by decide
    exact hvals _ _ hy
  have hc1 : mat g i₀ i₀ = 1 := by
    rw [hc0, hf1]
    exact SkewMonoidAlgebra.single_one_one
  apply Subtype.ext
  apply Units.ext
  show mat g = mat (1 : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))
  rw [hscalar, hc1]
  simp [mat]

/-- **tex l.161, as printed**: for `1 ≠ g ∈ EL_n(R)`, some `h = e_{ij}(e_V)` with `V` small and
nonempty does not commute with `g`. -/
theorem exists_isSmall_not_commute_elGen
    (hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z))
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {n : ℕ} (hn : 2 ≤ n)
    {g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)}
    (hD : ∀ (p q : Fin n) (ξ : Λ), ξ ∈ SkewMonoidAlgebra.support (mat g p q) → ξ ∈ D)
    (hg1 : g ≠ 1) :
    ∃ (V : Set Z) (hV : IsClopen V), V.Nonempty ∧ IsSmall D B F V ∧
      ∃ (i j : Fin n) (hij : i ≠ j),
        ¬ Commute g (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV))) := by
  by_contra hne
  refine hg1 (eq_one_of_commute_elGen_small hact hfree D B F hn
    (fun V hV hVne hs i j hij => ?_) hD)
  by_contra hc
  exact hne ⟨V, hV, hVne, hs, i, j, hij, hc⟩

/-- **tex l.161–174, as printed**: for a group acting topologically freely by homeomorphisms on a
totally separated space, and `1 ≠ g ∈ EL_n(LC(Z, F₂) ⋊ Λ)`, `n ≥ 2`, some `e_{ij}(e_V)` with `V`
small and nonempty does not commute with `g`. -/
def PrintedGeneralNonCommutingRoot : Prop :=
  ∀ (Λ Z : Type) [Group Λ] [TopologicalSpace Z] [TotallySeparatedSpace Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))],
    (∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z)) →
    (∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) →
    ∀ (n : ℕ), 2 ≤ n →
    ∀ g : elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ), g ≠ 1 →
    ∀ (D B : Finset Λ) (F : Finset (LocallyConstant Z (ZMod 2))),
      (∀ (p q : Fin n) (ξ : Λ), ξ ∈ SkewMonoidAlgebra.support (mat g p q) → ξ ∈ D) →
      ∃ (V : Set Z) (hV : IsClopen V), V.Nonempty ∧ IsSmall D B F V ∧
        ∃ (i j : Fin n) (hij : i ≠ j),
          ¬ Commute g
            (elGen i j hij (SkewMonoidAlgebra.single (1 : Λ) (LocallyConstant.charFn (ZMod 2) hV)))

theorem printedGeneralNonCommutingRoot : PrintedGeneralNonCommutingRoot :=
  fun _ _ _ _ _ _ _ _ hact hfree _ hn _ hg1 D B F hD =>
    exists_isSmall_not_commute_elGen hact hfree D B F hn hD hg1

end General
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.eq_one_of_commute_elGen_small
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_isSmall_not_commute_elGen
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.General.printedGeneralNonCommutingRoot
