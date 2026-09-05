import GroupApproximation.CharClass.ThomPuncturedRecursion
import GroupApproximation.CharClass.EulerLocalChart
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Top-punctured acyclicity of a `Fin`-indexed product

`ThomPuncturedRecursion.lean` propagates top-punctured acyclicity through a *binary*
product.  The base `M := S⁵ × ∏_{j < l} CP(d_j)` of the LIX obstruction has its
projective part as a dependent product `∀ j : Fin l, CP (d j)`
(`Analysis/LIXBlockProjections.lean`'s `baseY`), so this file iterates the binary step
over `Fin (n + 1)`.

## Main results

* `piFinSuccHomeo` — `(∀ i : Fin (n+1), X i) ≃ₜ X 0 × (∀ i : Fin n, X i.succ)`.
* `PuncturedAcyclic.congr` — top-punctured acyclicity transports along a homeomorphism.
* `puncturedAcyclic_pi` — a nonempty finite product of top-punctured acyclic spaces is
  top-punctured acyclic, of the summed dimension.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Splitting the first factor off a finite product of spaces.** -/
def piFinSuccHomeo {n : ℕ} (X : Fin (n + 1) → Type) [∀ i, TopologicalSpace (X i)] :
    (∀ i, X i) ≃ₜ X 0 × (∀ i : Fin n, X (Fin.succ i)) where
  toFun f := (f 0, fun i => f (Fin.succ i))
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  continuous_toFun :=
    (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply (Fin.succ i))
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      exact continuous_fst
    | succ j =>
      simp only [Fin.cons_succ]
      exact (continuous_apply j).comp continuous_snd

namespace PuncturedAcyclic

/-- **Top-punctured acyclicity transports along a homeomorphism.**  Both halves are
`CohomologyToolkit.homeo`: the first directly, the second after restricting the
homeomorphism to the punctured spaces (`homeomorphCompl`). -/
theorem congr (T : CohomologyToolkit) {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
    {d : ℕ} {z : Z} (e : Z ≃ₜ W) (h : PuncturedAcyclic W d (e z)) :
    PuncturedAcyclic Z d z :=
  ⟨h.pos, fun k hk => T.homeo _ _ e k (h.vanish k hk),
    fun k hk => T.homeo _ _ (homeomorphCompl e z) k (h.puncturedVanish k hk)⟩

end PuncturedAcyclic

/-- **A nonempty finite product of top-punctured acyclic spaces is top-punctured
acyclic**, of the summed dimension.  This is the form in which Step C uses the
recursion for `N = S¹ × S⁵ × ∏_j CP(d_j)`: apply it to the projective part and then
two binary steps, or apply it once to the whole family. -/
theorem puncturedAcyclic_pi (T : CohomologyToolkit) {n : ℕ} :
    ∀ (X : Fin (n + 1) → Type) [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)]
      (d : Fin (n + 1) → ℕ) (z : ∀ i, X i),
      (∀ i, PuncturedAcyclic (X i) (d i) (z i)) →
      PuncturedAcyclic (∀ i, X i) (∑ i, d i) z := by
  induction n with
  | zero =>
    intro X _ _ d z h
    haveI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    rw [Fin.sum_univ_one d]
    exact PuncturedAcyclic.congr T (Homeomorph.piUnique X) (h 0)
  | succ m ih =>
    intro X _ _ d z h
    rw [Fin.sum_univ_succ]
    refine PuncturedAcyclic.congr T (piFinSuccHomeo X) ?_
    exact PuncturedAcyclic.prod T (h 0)
      (ih (fun i => X (Fin.succ i)) (fun i => d (Fin.succ i)) (fun i => z (Fin.succ i))
        (fun i => h (Fin.succ i)))

end GroupApproximation.CharClass
