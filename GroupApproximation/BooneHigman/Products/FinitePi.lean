import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.Algebra.ProductFinitePresentation

/-!
# Finite products of finitely presented groups

The product step of the Boone–Higman assembly embeds a finitely generated metabelian group in a
finite direct product of pieces, each contained in a finitely presented self-similar group.  The
product of those hosts has to be finitely presented.  This module closes finite presentability
under finite direct products, by induction on the number of factors from the binary case
`GroupApproximation.ProductFinitePresentation.instProd`.

* `piFinSuccMulEquiv`: `∀ i : Fin (n + 1), G i ≃* G 0 × ∀ i : Fin n, G i.succ`.
* `isFinitelyPresented_pi_fin`: `∀ i : Fin n, G i` is finitely presented when every `G i` is.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Products

universe v

/-- Splitting off the first factor of a `Fin (n + 1)`-indexed direct product. -/
def piFinSuccMulEquiv {n : ℕ} (G : Fin (n + 1) → Type v) [∀ i, Group (G i)] :
    (∀ i, G i) ≃* G 0 × ∀ i : Fin n, G i.succ where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    obtain ⟨a, b⟩ := p
    exact Prod.ext (Fin.cons_zero (α := G) a b) (funext fun i => Fin.cons_succ (α := G) a b i)
  map_mul' _ _ := rfl

/-- **Finite direct products of finitely presented groups are finitely presented.** -/
theorem isFinitelyPresented_pi_fin (n : ℕ) (G : Fin n → Type v) [∀ i, Group (G i)]
    [∀ i, Group.IsFinitelyPresented (G i)] : Group.IsFinitelyPresented (∀ i, G i) := by
  induction n with
  | zero =>
    haveI : Unique (∀ i : Fin 0, G i) := Pi.uniqueOfIsEmpty G
    haveI : Finite (∀ i : Fin 0, G i) := Finite.of_subsingleton
    infer_instance
  | succ n ih =>
    haveI : Group.IsFinitelyPresented (∀ i : Fin n, G i.succ) := ih (fun i => G i.succ)
    exact Group.IsFinitelyPresented.equiv (piFinSuccMulEquiv G).symm

end Products
end BooneHigman
end GroupApproximation
