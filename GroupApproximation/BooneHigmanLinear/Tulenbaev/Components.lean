import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.AtPrime
import GroupApproximation.Meta.AxiomGuard

/-!
# The two Steinberg-level inputs of Tulenbaev's early stability theorem (lane sk-k2-loc)

Route A's owed char-`p` input is `BooneHigmanLinear.PolyFpK2VanishingGeTwoStatement`, i.e.
`K₂(N, F_p[s₁..s_k]) = ⊥` for `k ≥ 2` and `N ≥ k + 4`. It follows from
`BooneHigmanLinear.TulenbaevPolyFpK2Statement` (`PolyFpK2.lean`), which is M. Tulenbaev's early
stability theorem, *The Steinberg group of a polynomial ring*, Mat. Sb. 117 (1982); Math. USSR Sb.
45 (1983). Lavrenov–Sinchuk, arXiv:1909.02637v7, §1, record it as
`K₂(A_ℓ, k[x₁..x_n]) ≅ K₂(A_ℓ, k)` for a field `k` and `ℓ ≥ 4`.

Tulenbaev's proof is the `K₂` analogue of Suslin's elementary `K₁` proof. It uses no higher
`K`-theory, and its two Steinberg-level inputs are stated here as Props.

* `StLocalGlobalStatementAt n₀`: the Quillen–Suslin local–global principle for `St_N`, `N ≥ n₀`.
  An element of `St_N(A[X])` whose image in every `St_N(A_𝔪[X])`, `𝔪` maximal, is constant is
  itself constant. Constant means equal to the constant embedding of its value at `X = 0`.
  Tulenbaev proved it for the linear case; Lavrenov–Sinchuk (refs. [15, 16] there) prove it for
  simply-laced `Φ` of rank `≥ 3`.
* `K2HorrocksStatementAt n₀`: the Horrocks theorem for `K₂(N, -)`, `N ≥ n₀` (Tulenbaev, Thm 5.1,
  as cited by Lavrenov–Sinchuk).
  - The square `K₂(N,A) → K₂(N,A[X])`, `K₂(N,A[X⁻¹]) → K₂(N,A[X,X⁻¹])` is a pullback.
  - `K₂(N,A[X]) → K₂(N,A[X,X⁻¹])` is injective.
  - `A[X⁻¹]` is modelled as a second copy of `A[X]` mapped by `X ↦ T⁻¹`.

**Rank bound.** The rank is a parameter `n₀`. The Props are asserted true at Tulenbaev's bound,
which is not yet read at source (the paper is behind the Math-Net.ru / MSI proxy). Nothing
downstream should fix `n₀` until someone reads it. With `n₀ = 5` (`ℓ ≥ 4`) the local–global Prop
matches Lavrenov–Sinchuk's rank `≥ 3` range.

**Not here.** The assembly, i.e. local–global + Horrocks + `K₂(N, F_p) = 0` + Nagata's change of
variables, induction on `k` ⇒ `TulenbaevPolyFpK2Statement`. That is lane bh-pal-wire's step (d).
No reduction theorem is claimed in this module.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace Tulenbaev

open GroupApproximation.SteinbergGroup Polynomial

/-- **Quillen–Suslin local–global principle for `St_N`**, at ranks `N ≥ n₀`. If `g ∈ St_N(A[X])`
becomes constant in `St_N(A_𝔪[X])` for every maximal ideal `𝔪`, then `g` is constant.
(Tulenbaev 1982; Lavrenov–Sinchuk, arXiv:1909.02637, §1.) -/
def StLocalGlobalStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] (N : ℕ), n₀ ≤ N →
    ∀ g : SteinbergGroup (Fin N) A[X],
      (∀ (M : Ideal A) [M.IsMaximal],
        ringMap (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M))) g =
          ringMap (Polynomial.C : Localization.AtPrime M →+* (Localization.AtPrime M)[X])
            (ringMap (algebraMap A (Localization.AtPrime M))
              (ringMap (Polynomial.evalRingHom (0 : A)) g))) →
      g = ringMap (Polynomial.C : A →+* A[X]) (ringMap (Polynomial.evalRingHom (0 : A)) g)

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.StLocalGlobalStatementAt

/-- The coordinate `A[X] → A[T, T⁻¹]`, `X ↦ T`. -/
noncomputable def toLaurentPos (A : Type) [CommRing A] : A[X] →+* LaurentPolynomial A :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T 1)

/-- The coordinate `A[X] → A[T, T⁻¹]`, `X ↦ T⁻¹`, modelling `A[X⁻¹] → A[X, X⁻¹]`. -/
noncomputable def toLaurentNeg (A : Type) [CommRing A] : A[X] →+* LaurentPolynomial A :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))

/-- **Horrocks theorem for `K₂(N, -)`**, at ranks `N ≥ n₀` (Tulenbaev, Thm 5.1).
`K₂(N, A[X]) → K₂(N, A[X, X⁻¹])` is injective, and an element of `K₂(N, A[X])` and an element
of `K₂(N, A[X⁻¹])` with the same image in `K₂(N, A[X, X⁻¹])` both come from one element of
`K₂(N, A)`. -/
def K2HorrocksStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] (N : ℕ), n₀ ≤ N →
    (∀ u ∈ BooneHigman.SteinbergBasic.K2 (Fin N) A[X], ringMap (toLaurentPos A) u = 1 → u = 1) ∧
    ∀ u ∈ BooneHigman.SteinbergBasic.K2 (Fin N) A[X],
      ∀ v ∈ BooneHigman.SteinbergBasic.K2 (Fin N) A[X],
        ringMap (toLaurentPos A) u = ringMap (toLaurentNeg A) v →
          ∃ w ∈ BooneHigman.SteinbergBasic.K2 (Fin N) A,
            ringMap (Polynomial.C : A →+* A[X]) w = u ∧ ringMap (Polynomial.C : A →+* A[X]) w = v

#audit_axioms GroupApproximation.BooneHigmanLinear.Tulenbaev.K2HorrocksStatementAt

end Tulenbaev
end BooneHigmanLinear
end GroupApproximation
