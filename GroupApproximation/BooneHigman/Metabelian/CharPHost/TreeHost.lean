import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeFaithful
import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeGroup
import GroupApproximation.BooneHigman.Metabelian.ChainCharP
import Mathlib.Algebra.Field.ZMod
import GroupApproximation.Meta.AxiomGuard

/-!
# The char-`p` parameter-coordinate affine host is self-similar and faithful (lane bh-met-02)

Research node `positive-char-polynomial-affine-groups-are-self-similar-proof`.  The tree
representation `treeRep i₀ n` of `R^n ⋊ E_n(R)`, `R = F[s_σ]` (file `TreeGroup`), is injective:
if `(b, g)` acts trivially, then `g(X, A) c + b(X, A) = c` for every `c ∈ F[X]^n` and every point
`A` (`eq_of_act_eq`, from `TreeEval` and `TreeFaithful`); with `c = 0` and `c = e_j`, and since
the evaluations `ev i₀ A` separate polynomials, `b = 0` and `g = 1`.

Endpoint: `charPAffineSelfSimilarStatement_holds` proves the interface
`Chain.CharPAffineSelfSimilarStatement` (consumed by `Chain.charPLinearHostStatement_of_chain`),
with `F = F_p`, `σ = Fin k`, uniformizer `s_0` (bh-met-01 convention) and the alphabet
`(Fin n → F_p) × ({i : Fin k // i ≠ 0} → F_p)` of size `p^n · p^(k-1)`.
-/

noncomputable section

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost
namespace TreeHost

open scoped Matrix Polynomial

section Fixed

variable {F : Type*} [Field F] {σ : Type*} [DecidableEq σ] (i₀ : σ) {m : Type*} [Fintype m]

/-- **A pair fixing every word is the identity along every line**: if `(g, b)` fixes every word,
then `g(X, A) c + b(X, A) = c` for all `c ∈ F[X]^m` and all points `A`. -/
theorem eq_of_act_eq (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F)
    (hact : ∀ w, act i₀ g b w = w) (A : σ → F[X]) (c : m → F[X]) (k : m) :
    (g.map (ev i₀ A) *ᵥ c) k + ev i₀ A (b k) = c k := by
  refine sub_eq_zero.1 (eq_zero_of_forall_X_pow_dvd fun j => ?_)
  obtain ⟨R, hR⟩ := exists_vecOf_act i₀ (wordOf i₀ j c A) g b
    (fun i => Polynomial.divX^[j] (A i)) (fun k => Polynomial.divX^[j] (c k))
  have hpt : withUniformizer i₀ Polynomial.X (listPoint Polynomial.X
      (params i₀ (wordOf i₀ j c A)) (fun i => Polynomial.divX^[j] (A i))) =
      withUniformizer i₀ Polynomial.X A := by
    funext i
    by_cases hi : i = i₀
    · simp only [withUniformizer, if_pos hi]
    · simp only [withUniformizer, if_neg hi]
      exact listPoint_wordOf i₀ j c A i hi
  have hev : ev i₀ (listPoint Polynomial.X
      (params i₀ (wordOf i₀ j c A)) (fun i => Polynomial.divX^[j] (A i))) = ev i₀ A := by
    rw [ev, ev, hpt]
  rw [hev, vecOf_wordOf i₀ j c A, hact] at hR
  have hs := vecOf_sub i₀ (wordOf i₀ j c A) R (fun k => Polynomial.divX^[j] (c k)) k
  rw [vecOf_wordOf i₀ j c A, length_wordOf i₀ j c A] at hs
  exact Dvd.intro (R k - Polynomial.divX^[j] (c k)) (by rw [hR k]; exact hs.symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.eq_of_act_eq

end Fixed

section Host

variable {F : Type} [Field F] {σ : Type} [DecidableEq σ] (i₀ : σ) {n : ℕ}

/-- **Faithfulness**: the tree representation of `R^n ⋊ E_n(R)`, `R = F[s_σ]`, is injective. -/
theorem treeRep_injective : Function.Injective (treeRep (F := F) i₀ n) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  have hact : ∀ w, act i₀ (affMat x) (affVec x) w = w := fun w => by
    have h1 : treeRep i₀ n x • w = (1 : Trees.TreeAut (Letter (Fin n) F i₀)) • w := by
      rw [hx]
    exact (treeRep_smul i₀ x w).symm.trans (h1.trans (one_smul _ w))
  have key := eq_of_act_eq i₀ (affMat x) (affVec x) hact
  have hb : affVec x = 0 := by
    funext k
    refine eq_zero_of_forall_ev i₀ fun A => ?_
    have h := key A 0 k
    simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_add] at h
    exact h
  have hg : affMat x = 1 := Matrix.ext fun k j => sub_eq_zero.1 <|
    eq_zero_of_forall_ev i₀ fun A => by
      have h := key A (Pi.single j 1) k
      rw [hb, Pi.zero_apply, map_zero, add_zero, Matrix.mulVec_single_one, Matrix.col_apply,
        Matrix.map_apply] at h
      rw [map_sub, h]
      by_cases hkj : k = j
      · rw [hkj, Pi.single_eq_same, Matrix.one_apply_eq, map_one, sub_self]
      · rw [Pi.single_eq_of_ne hkj, Matrix.one_apply_ne hkj, map_zero, sub_zero]
  exact SemidirectProduct.ext (Multiplicative.toAdd.injective (hb.trans affVec_one.symm))
    (Subtype.ext (Units.ext (hg.trans affMat_one.symm)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.treeRep_injective

/-- **The affine host is self-similar and faithful**. -/
theorem isSelfSimilarRep_treeRep : Trees.IsSelfSimilarRep (treeRep (F := F) i₀ n) :=
  ⟨treeRep_injective i₀, isSelfSimilar_treeRep i₀⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.isSelfSimilarRep_treeRep

end Host

/-- **Research node `positive-char-polynomial-affine-groups-are-self-similar`** (lane bh-met-02):
the affine host `F_p[s_0, …, s_{k-1}]^n ⋊ E_n` acts faithfully and self-similarly on the tree over
`F_p^n × F_p^(k-1)`, with uniformizer `s_0`. -/
theorem charPAffineSelfSimilarStatement_holds : Chain.CharPAffineSelfSimilarStatement := by
  intro p _ k n hk hn
  haveI : NeZero k := ⟨by omega⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact ⟨Letter (Fin n) (ZMod p) (0 : Fin k), inferInstance, inferInstance,
    treeRep (F := ZMod p) (0 : Fin k) n, isSelfSimilarRep_treeRep (0 : Fin k)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.charPAffineSelfSimilarStatement_holds

end TreeHost
end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation

end
