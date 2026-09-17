import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimplicitySteps.Setup
import Mathlib.GroupTheory.Commutator.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity, Step 1: a nontrivial commutator with a small elementary matrix

`simple_kazhdan_sofic_group.tex`, subsection "Simplicity", Step 1, tex l.265–269:

> The coefficients at $u_e$ agree on every small $V$, so they agree everywhere. (l.265–266)
> Therefore $g=cI_3$ with $c\in\LC(C,\F_2)$, and comparing coefficients at $u_e$ in $cc^{-1}=1$
> gives $c=1$ and $g=1$. (l.267–268) Fix such $h$ and $V$. (l.268) Then $x=[g,h]$ lies in
> $K\setminus\{1\}$. (l.268–269)

Setting: `G = EL_n(R)` with `R = ClopenGroupCrossedProduct Λ Z (ZMod 2)`; `w` bounds the word
lengths of the support of the entries of `g` (and `g⁻¹`), and "small" is `IsPrintedSmall T w g`.
The standing hypothesis of these sentences ("suppose `g` commutes with every `e_{ij}(e_V)`, `V`
small and nonempty") is printed in the argument (tex l.253–255) and appears as the hypothesis `hg`.

Proof route:

* the bridge to `General.coeff_one_diag_eq` and `General.eq_one_of_commute_elGen_small`, which are
  stated over `SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ` (definitionally the crossed
  product), with the action `(ξ • f) z = f (ξ⁻¹ • z)`; "small" over the balls follows from
  `General.IsSmall` over their finite sets (`isPrintedSmall_of_isSmall`);
* `g = cI` with `g g⁻¹ = 1` gives `c · (g⁻¹)_{i₀i₀} = 1`; taking the coefficient at `u_e` gives
  `c · f = 1` in `LC(Z, F_2)`, so `c = 1` pointwise in `F_2`, hence `g = I`;
* the commutator `[g, h] = g · (h g⁻¹ h⁻¹)` lies in the normal subgroup `K`, and is `≠ 1` because
  `g` and `h` do not commute.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SimplicitySteps

open scoped Pointwise commutatorElement

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]

/-- If `g` commutes with every `e_{ij}(e_V)` with `V` small and nonempty, then `g = 1`. -/
theorem eq_one_of_forall_commute_small [TotallySeparatedSpace Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {T : Set Λ} (hT : T.Finite)
    (w : ℕ) {n : ℕ} (hn : 2 ≤ n)
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
    (hw : ∀ (p q : Fin n) (ξ : Λ), ξ ∈ SkewMonoidAlgebra.support (General.mat g p q) →
      ξ ∈ wordBall T w)
    (hg : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsPrintedSmall T w g V →
      ∀ (i j : Fin n) (hij : i ≠ j),
        Commute g (elGen i j hij
          (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV)))) :
    g = 1 := by
  letI : MulSemiringAction Λ (LocallyConstant Z (ZMod 2)) :=
    ClopenGroupCoeff.instMulSemiringAction Λ Z (ZMod 2)
  have hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z) :=
    fun _ _ _ => rfl
  have hmono : wordBall T w ⊆ wordBall T (2 * w) := wordBall_mono T (by omega)
  exact General.eq_one_of_commute_elGen_small (g := g) hact hfree
    (finite_wordBall hT (2 * w)).toFinset (finite_wordBall hT w).toFinset (coeffFinset g) hn
    (fun V hV hVne hs p q hpq => hg V hV hVne (isPrintedSmall_of_isSmall hT w g hV hs) p q hpq)
    (fun p q ξ hξ => (finite_wordBall hT (2 * w)).mem_toFinset.mpr (hmono (hw p q ξ hξ)))

/-- **tex l.265–266**: if `g` commutes with every `e_{ij}(e_V)` with `V` small and nonempty, the
coefficients at `u_e` of the diagonal entries agree on every small `V`, so they agree everywhere:
`(g_{ii})_e = (g_{jj})_e` in `LC(Z, F_2)` for all `i, j`. -/
theorem manuscriptSentence_coeffOneAgreeEverywhere [TotallySeparatedSpace Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {T : Set Λ} (hT : T.Finite)
    (w : ℕ) {n : ℕ} (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
    (hg : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsPrintedSmall T w g V →
      ∀ (i j : Fin n) (hij : i ≠ j),
        Commute g (elGen i j hij
          (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV))))
    (i j : Fin n) :
    SkewMonoidAlgebra.coeff (General.mat g i i) 1 = SkewMonoidAlgebra.coeff (General.mat g j j) 1 := by
  by_cases hij : i = j
  · rw [hij]
  · letI : MulSemiringAction Λ (LocallyConstant Z (ZMod 2)) :=
      ClopenGroupCoeff.instMulSemiringAction Λ Z (ZMod 2)
    have hact : ∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z) :=
      fun _ _ _ => rfl
    exact General.coeff_one_diag_eq (g := g) hact hfree
      (finite_wordBall hT (2 * w)).toFinset (finite_wordBall hT w).toFinset (coeffFinset g)
      (fun V hV hVne hs p q hpq => hg V hV hVne (isPrintedSmall_of_isSmall hT w g hV hs) p q hpq)
      hij

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.manuscriptSentence_coeffOneAgreeEverywhere

/-- **tex l.267–268, second clause**: if `g = cI` with `c ∈ LC(Z, F_2)`, comparing coefficients at
`u_e` in `c c⁻¹ = 1` gives `c = 1` and `g = 1`. -/
theorem eq_one_of_mat_eq_scalar {n : ℕ} (hn : 3 ≤ n)
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
    (c : LocallyConstant Z (ZMod 2))
    (hscalar : General.mat g = Matrix.scalar (Fin n) (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) c)) :
    c = 1 ∧ g = 1 := by
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hinv : ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) c * General.mat g⁻¹ i₀ i₀ = 1 := by
    have h1 : General.mat g * General.mat g⁻¹ = 1 :=
      Units.mul_inv (g : (Matrix (Fin n) (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))ˣ)
    rw [hscalar] at h1
    have h2 := congrFun (congrFun h1 i₀) i₀
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.one_apply_eq] at h2
    exact h2
  have hc1 : c = 1 := by
    have h2 : SkewMonoidAlgebra.coeff
          (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) c * General.mat g⁻¹ i₀ i₀) 1 =
        SkewMonoidAlgebra.coeff (1 : ClopenGroupCrossedProduct Λ Z (ZMod 2)) 1 := by
      rw [hinv]
    rw [ClopenGroupCrossedProduct.coeff_apply, SkewMonoidAlgebra.coeff_single_one_mul,
      SkewMonoidAlgebra.coeff_one, Finsupp.single_eq_same] at h2
    have h3 := DFunLike.congr_arg (ClopenGroupCoeff.of Λ Z (ZMod 2)).symm h2
    rw [map_mul, map_one, RingEquiv.symm_apply_apply] at h3
    refine LocallyConstant.ext fun y => ?_
    have hy := LocallyConstant.congr_fun h3 y
    rw [LocallyConstant.mul_apply, LocallyConstant.one_apply] at hy
    rw [LocallyConstant.one_apply]
    have hvals : ∀ a b : ZMod 2, a * b = 1 → a = 1 := by decide
    exact hvals _ _ hy
  refine ⟨hc1, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show General.mat g =
    General.mat (1 : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
  rw [hscalar, hc1]
  simp [General.mat]

/-- **tex l.267–268**: if `g` commutes with every `e_{ij}(e_V)` with `V` small and nonempty, then
`g = cI` with `c ∈ LC(Z, F_2)`; and for any such `c`, comparing coefficients at `u_e` in `cc⁻¹ = 1`
gives `c = 1` and `g = 1`. -/
theorem manuscriptSentence_scalarThenIdentity [TotallySeparatedSpace Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {T : Set Λ} (hT : T.Finite)
    (w : ℕ) {n : ℕ} (hn : 3 ≤ n)
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
    (hw : ∀ (p q : Fin n) (ξ : Λ), ξ ∈ SkewMonoidAlgebra.support (General.mat g p q) →
      ξ ∈ wordBall T w)
    (hg : ∀ (V : Set Z) (hV : IsClopen V), V.Nonempty → IsPrintedSmall T w g V →
      ∀ (i j : Fin n) (hij : i ≠ j),
        Commute g (elGen i j hij
          (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV)))) :
    (∃ c : LocallyConstant Z (ZMod 2),
        General.mat g = Matrix.scalar (Fin n) (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) c)) ∧
      ∀ c : LocallyConstant Z (ZMod 2),
        General.mat g = Matrix.scalar (Fin n) (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) c) →
          c = 1 ∧ g = 1 := by
  have h1 := eq_one_of_forall_commute_small hfree hT w (by omega) g hw hg
  refine ⟨⟨1, ?_⟩, fun c hc => eq_one_of_mat_eq_scalar hn g c hc⟩
  rw [h1]
  simp [General.mat]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.manuscriptSentence_scalarThenIdentity

/-- In a normal subgroup, the commutator of a member with a non-commuting element is a nontrivial
member. -/
theorem commutator_mem_and_ne_one {Γ : Type*} [Group Γ] {K : Subgroup Γ} (hK : K.Normal)
    {g h : Γ} (hgK : g ∈ K) (hgh : ¬ Commute g h) : ⁅g, h⁆ ∈ K ∧ ⁅g, h⁆ ≠ 1 := by
  refine ⟨?_, fun h1 => hgh (commutatorElement_eq_one_iff_commute.mp h1)⟩
  have hm := K.mul_mem hgK (hK.conj_mem g⁻¹ (K.inv_mem hgK) h)
  rw [commutatorElement_def]
  simpa only [mul_assoc] using hm

/-- **tex l.268, "Fix such `h` and `V`"**: for `1 ≠ g`, with `w` bounding the word lengths of the
entries of `g` and `g⁻¹`, there are a nonempty small clopen `V` and `h = e_{ij}(e_V)` not commuting
with `g`. -/
theorem manuscriptSentence_existsNonCommutingSmallRoot [TotallySeparatedSpace Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {T : Set Λ} (hT : T.Finite)
    (w : ℕ) {n : ℕ} (hn : 3 ≤ n)
    {g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))}
    (hw : ∀ (p q : Fin n) (ξ : Λ),
      (ξ ∈ SkewMonoidAlgebra.support (General.mat g p q) ∨
          ξ ∈ SkewMonoidAlgebra.support (General.mat g⁻¹ p q)) →
        ξ ∈ wordBall T w)
    (hg1 : g ≠ 1) :
    ∃ (V : Set Z) (hV : IsClopen V), V.Nonempty ∧ IsPrintedSmall T w g V ∧
      ∃ (i j : Fin n) (hij : i ≠ j),
        ¬ Commute g (elGen i j hij
          (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV))) := by
  by_contra hne
  refine hg1 (eq_one_of_forall_commute_small hfree hT w (by omega) g
    (fun p q ξ hξ => hw p q ξ (Or.inl hξ)) fun V hV hVne hs i j hij => ?_)
  by_contra hc
  exact hne ⟨V, hV, hVne, hs, i, j, hij, hc⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.manuscriptSentence_existsNonCommutingSmallRoot

/-- **tex l.268–269**: for `1 ≠ g ∈ K ⊴ G`, with `h = e_{ij}(e_V)`, `V` small and nonempty, not
commuting with `g`, the commutator `x = [g, h]` lies in `K ∖ {1}`. -/
theorem manuscriptSentence_commutatorInKMinusOne [TotallySeparatedSpace Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {T : Set Λ} (hT : T.Finite)
    (w : ℕ) {n : ℕ} (hn : 3 ≤ n)
    (K : Subgroup (elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))
    (hK : K.Normal) {g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))}
    (hgK : g ∈ K)
    (hw : ∀ (p q : Fin n) (ξ : Λ),
      (ξ ∈ SkewMonoidAlgebra.support (General.mat g p q) ∨
          ξ ∈ SkewMonoidAlgebra.support (General.mat g⁻¹ p q)) →
        ξ ∈ wordBall T w)
    (hg1 : g ≠ 1) :
    ∃ (V : Set Z) (hV : IsClopen V), V.Nonempty ∧ IsPrintedSmall T w g V ∧
      ∃ (i j : Fin n) (hij : i ≠ j),
        ⁅g, elGen i j hij
            (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV))⁆ ∈ K ∧
          ⁅g, elGen i j hij
            (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV))⁆ ≠ 1 := by
  obtain ⟨V, hV, hVne, hs, i, j, hij, hc⟩ :=
    manuscriptSentence_existsNonCommutingSmallRoot hfree hT w hn hw hg1
  exact ⟨V, hV, hVne, hs, i, j, hij, commutator_mem_and_ne_one hK hgK hc⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.manuscriptSentence_commutatorInKMinusOne

end SimplicitySteps
end SimpleKazhdanSofic
end GroupApproximation
