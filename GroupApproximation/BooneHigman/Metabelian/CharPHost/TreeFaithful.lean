import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeEval
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.MvPolynomial.Funext
import GroupApproximation.Meta.AxiomGuard

/-!
# Pairs acting trivially on the tree (lane bh-met-02)

Faithfulness step of lane bh-met-02.  Every `c ∈ F[X]^m` and point `A ∈ F[X]^σ` is realized to
`X`-adic precision `j` by a word: `wordOf j c A` has digits the first `j` coefficients of `c`
and parameters the first `j` coefficients of `A`, so `vecOf (wordOf j c A) (divX^j c) = c`
(`vecOf_wordOf`) and it moves the tail point `divX^j A` back to `A` (`listPoint_wordOf`).  If
`(g, b)` fixes every word, `exists_vecOf_act` gives `g(X, A) c + b(X, A) ≡ c mod X^j` for all
`j`, hence `g(X, A) c + b(X, A) = c` (`eq_of_act_eq`).  The evaluations `ev i₀ A` separate
polynomials (`eq_zero_of_forall_ev`, from `MvPolynomial.funext` over the infinite domain `F[X]`),
which is used in `TreeHost` to conclude `(g, b) = (1, 0)`.
-/

noncomputable section

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost
namespace TreeHost

open MvPolynomial
open scoped Matrix Polynomial

/-- A polynomial divisible by every power of `X` is zero. -/
theorem eq_zero_of_forall_X_pow_dvd {F : Type*} [Field F] {p : F[X]}
    (h : ∀ j : ℕ, Polynomial.X ^ j ∣ p) : p = 0 := by
  by_contra hp
  have h1 := Polynomial.natDegree_le_of_dvd (h (p.natDegree + 1)) hp
  rw [Polynomial.natDegree_X_pow] at h1
  omega

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.eq_zero_of_forall_X_pow_dvd

variable {F : Type*} [Field F] {σ : Type*} [DecidableEq σ] (i₀ : σ)

/-! ### Separating polynomials by evaluations along lines -/

/-- `F[s_σ] → F[X][s_σ]`, replacing the uniformizer `s_{i₀}` by the constant `X`. -/
def embed : MvPolynomial σ F →+* MvPolynomial σ F[X] :=
  eval₂Hom ((C : F[X] →+* MvPolynomial σ F[X]).comp Polynomial.C)
    fun i => if i = i₀ then C Polynomial.X else X i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.embed

/-- `F[X][s_σ] → F[s_σ]`, sending `X` back to `s_{i₀}`. -/
def retract : MvPolynomial σ F[X] →+* MvPolynomial σ F :=
  eval₂Hom (Polynomial.eval₂RingHom C (X i₀)) X

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.retract

theorem retract_embed : (retract i₀).comp (embed i₀) = RingHom.id (MvPolynomial σ F) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · show retract i₀ (embed i₀ (C r)) = C r
    rw [embed, eval₂Hom_C, RingHom.comp_apply, retract, eval₂Hom_C, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C]
  · show retract i₀ (embed i₀ (X i)) = X i
    rw [embed, eval₂Hom_X']
    show retract i₀ (if i = i₀ then C Polynomial.X else X i) = X i
    by_cases hi : i = i₀
    · rw [if_pos hi, retract, eval₂Hom_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hi]
    · rw [if_neg hi, retract, eval₂Hom_X']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.retract_embed

theorem eval_embed (B : σ → F[X]) (Q : MvPolynomial σ F) : eval B (embed i₀ Q) = ev i₀ B Q := by
  have h : (eval B).comp (embed i₀) = ev i₀ B := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · show eval B (embed i₀ (C r)) = ev i₀ B (C r)
      rw [embed, eval₂Hom_C, RingHom.comp_apply, eval_C, ev_C]
    · show eval B (embed i₀ (X i)) = aeval (withUniformizer i₀ Polynomial.X B) (X i)
      rw [embed, eval₂Hom_X', aeval_X]
      show eval B (if i = i₀ then C Polynomial.X else X i) =
        (if i = i₀ then Polynomial.X else B i)
      by_cases hi : i = i₀
      · rw [if_pos hi, if_pos hi, eval_C]
      · rw [if_neg hi, if_neg hi, eval_X]
  exact RingHom.congr_fun h Q

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.eval_embed

/-- **The evaluations along lines separate polynomials.** -/
theorem eq_zero_of_forall_ev {Q : MvPolynomial σ F} (h : ∀ A : σ → F[X], ev i₀ A Q = 0) :
    Q = 0 := by
  have h1 : embed i₀ Q = 0 := MvPolynomial.funext fun B => by
    rw [eval_embed, h, map_zero]
  have h2 := RingHom.congr_fun (retract_embed i₀) Q
  rw [RingHom.comp_apply, h1, map_zero, RingHom.id_apply] at h2
  exact h2.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.eq_zero_of_forall_ev

/-! ### Words realizing polynomial vectors -/

variable {m : Type*} [Fintype m]

/-- The word of the first `j` coefficients of `c` (digits) and of `A` (parameters). -/
def wordOf : ℕ → (m → F[X]) → (σ → F[X]) → List (Letter m F i₀)
  | 0, _, _ => []
  | j + 1, c, A => (fun k => (c k).coeff 0, fun i => (A i.1).coeff 0) ::
      wordOf j (fun k => (c k).divX) (fun i => (A i).divX)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.wordOf

theorem length_wordOf (j : ℕ) : ∀ (c : m → F[X]) (A : σ → F[X]), (wordOf i₀ j c A).length = j := by
  induction j with
  | zero => intro c A; rfl
  | succ j ih =>
    intro c A
    exact congrArg Nat.succ (ih (fun k => (c k).divX) (fun i => (A i).divX))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.length_wordOf

theorem vecOf_wordOf (j : ℕ) : ∀ (c : m → F[X]) (A : σ → F[X]),
    vecOf i₀ (wordOf i₀ j c A) (fun k => Polynomial.divX^[j] (c k)) = c := by
  induction j with
  | zero => intro c A; rfl
  | succ j ih =>
    intro c A
    have h := ih (fun k => (c k).divX) (fun i => (A i).divX)
    funext k
    show Polynomial.C ((c k).coeff 0) + Polynomial.X *
      vecOf i₀ (wordOf i₀ j (fun k => (c k).divX) (fun i => (A i).divX))
        (fun k => Polynomial.divX^[j] (c k).divX) k = c k
    rw [h, add_comm]
    exact Polynomial.X_mul_divX_add (c k)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.vecOf_wordOf

theorem listPoint_wordOf (j : ℕ) : ∀ (c : m → F[X]) (A : σ → F[X]) (i : σ), i ≠ i₀ →
    listPoint Polynomial.X (params i₀ (wordOf i₀ j c A)) (fun i => Polynomial.divX^[j] (A i)) i =
      A i := by
  induction j with
  | zero => intro c A i _; rfl
  | succ j ih =>
    intro c A i hi
    have h := ih (fun k => (c k).divX) (fun i => (A i).divX) i hi
    show algebraMap F F[X] (extParam i₀ (fun i : {i : σ // i ≠ i₀} => (A i.1).coeff 0) i) +
      Polynomial.X * listPoint Polynomial.X
        (params i₀ (wordOf i₀ j (fun k => (c k).divX) (fun i => (A i).divX)))
        (fun i => Polynomial.divX^[j] (A i).divX) i = A i
    rw [h, extParam, dif_neg hi, Polynomial.algebraMap_eq, add_comm]
    exact Polynomial.X_mul_divX_add (A i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.listPoint_wordOf

theorem vecOf_sub (w : List (Letter m F i₀)) (v v' : m → F[X]) (k : m) :
    vecOf i₀ w v k - vecOf i₀ w v' k = Polynomial.X ^ w.length * (v k - v' k) := by
  induction w with
  | nil =>
    show v k - v' k = Polynomial.X ^ 0 * (v k - v' k)
    rw [pow_zero, one_mul]
  | cons x u ih =>
    show (Polynomial.C (x.1 k) + Polynomial.X * vecOf i₀ u v k) -
      (Polynomial.C (x.1 k) + Polynomial.X * vecOf i₀ u v' k) =
        Polynomial.X ^ (u.length + 1) * (v k - v' k)
    linear_combination Polynomial.X * ih

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.vecOf_sub

end TreeHost
end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation

end
