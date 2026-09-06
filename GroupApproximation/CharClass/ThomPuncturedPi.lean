import GroupApproximation.CharClass.ThomPuncturedRecursion
import GroupApproximation.CharClass.EulerLocalChart
import Mathlib.Data.Fin.Tuple.Basic

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
* there is deliberately no `Fin`-indexed recursion; see the last section for why.
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

/-- **A one-factor product is its only factor.**  Stated through `piFinSuccHomeo` and
`Homeomorph.prodUnique` rather than `Homeomorph.piUnique`, so that the underlying map is
literally `fun f => f 0` and no `default` ever appears. -/
def piFinOneHomeo (X : Fin 1 → Type) [∀ i, TopologicalSpace (X i)] :
    (∀ i, X i) ≃ₜ X 0 :=
  (piFinSuccHomeo X).trans (Homeomorph.prodUnique (X 0) (∀ i : Fin 0, X (Fin.succ i)))

namespace PuncturedAcyclic

/-- **Top-punctured acyclicity transports along a homeomorphism.**  Both halves are
`CohomologyToolkit.homeo`: the first directly, the second after restricting the
homeomorphism to the punctured spaces (`homeomorphCompl`). -/
theorem congr (T : CohomologyToolkit) {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
    {d : ℕ} {z : Z} (e : Z ≃ₜ W) (h : PuncturedAcyclic W d (e z)) :
    PuncturedAcyclic Z d z :=
  ⟨h.pos, fun k hk => T.homeo _ _ e k (h.vanish k hk),
    fun k hk => T.homeo _ _ (homeomorphCompl e z) k (h.puncturedVanish k hk)⟩

/-- **Transport with the image of the point named separately.**  The convenient form when
the homeomorphism is a symmetry of the space carrying an arbitrary point to a
distinguished one: `CP d` is homogeneous, so a unitary conjugation carries the zero `z`
to the base point, and top-punctured acyclicity at the base point transports to `z`. -/
theorem congr' (T : CohomologyToolkit) {Z W : Type} [TopologicalSpace Z]
    [TopologicalSpace W] {d : ℕ} {z : Z} {w : W} (e : Z ≃ₜ W) (hw : e z = w)
    (h : PuncturedAcyclic W d w) : PuncturedAcyclic Z d z :=
  congr T e (by rw [hw]; exact h)

end PuncturedAcyclic

/-! ## Iterating the binary step

There is deliberately no `Fin`-indexed version of `PuncturedAcyclic.prod` here.  The
Künneth input is per-factor (`KunnethFactor Y`, see `ThomPuncturedRecursion.lean`), and
only spheres, complex projective spaces and cohomologically invisible factors are
available as Künneth factors — a *product* of them is not.  So an iterated product must
be nested with the simple factor on the right,

```text
N = (((S¹ × S⁵) × CP d₁) × CP d₂) × ⋯,
```

and built by chaining `PuncturedAcyclic.prod` one factor at a time, each step supplying
the two `KunnethFactor` instances for that step's right-hand factor.  A `Fin`-indexed
statement splitting off the *first* factor would put the tail product in the second
slot, where no Künneth factor exists.

`piFinSuccHomeo`, `piFinOneHomeo` and `PuncturedAcyclic.congr`/`congr'` remain, since
they are what transports the result onto a dependent product such as
`Analysis/LIXBlockProjections`'s `baseY` once it has been built by chaining.
-/

end GroupApproximation.CharClass
