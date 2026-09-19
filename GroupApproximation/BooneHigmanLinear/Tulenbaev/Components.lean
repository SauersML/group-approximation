import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.AtPrime.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The Steinberg-level inputs of Tulenbaev's stability theorem (lane sk-k2-loc)

Source, read at source (the English translation, via Math-Net.ru): M. S. Tulenbaev, *The Steinberg
group of a polynomial ring*, Mat. Sb. 117(159) (1982), 131–144; Math. USSR Sb. 45 (1983),
139–154. "Ring" there means commutative with unity.

* **Thm 2.1** (p.143). Let `r ≥ 5` and `α ∈ St_r(A[X], XA[X])`. Then `α = 1` iff for every maximal
  ideal `𝔐` the image of `α` in `St_r(A_𝔐[X])` is `1`. Here `St_r(A[X], XA[X])` embeds in
  `St_r(A[X])` as the kernel of `X ↦ 0` (Prop 1.6, the split `St_r(A[X]) ≅ St_r(A) ⋉ St_r(A[X], XA[X])`).
  So Thm 2.1 is `StLocalGlobalStatementAt 5`: "constant" below means equal to the constant
  embedding of the value at `X = 0`. The equivalence of the two forms is on paper only (via Prop
  1.6) and is not proved in Lean here.
* **Thm 5.1(a)** (p.152). For `r ≥ 5` and any ring `A`, `St_r(A[X]) → St_r(A[X,X⁻¹]) ← St_r(A[X⁻¹])`
  are injective, and the intersection of their images is `St_r(A)`. This is
  `TulenbaevHorrocks.StHorrocksStatementAt 5` (lane pal-q111, `TulenbaevHorrocks/Statements.lean`).
  The `K₂` form `K2HorrocksStatementAt 5` follows from it on paper.
* **Thm 5.3** (p.153, the main theorem). For `A` noetherian and `B = A[X₁..X_n]`,
  `K_{2,r}(B) → K₂(B)` is surjective for `r ≥ max(4, dim A + 2)` and injective for
  `r ≥ max(5, dim A + 3)`.

**LOUD: what Tulenbaev does NOT give.**
- Thm 5.3 is a *stability* theorem. It identifies `K₂(r, F_p[x₁..x_k])` with the stable
  `K₂(F_p[x₁..x_k])` for `r ≥ 5`.
- The vanishing `BooneHigmanLinear.TulenbaevPolyFpK2Statement` needs, in addition, stable
  `K₂(F_p[x₁..x_k]) = K₂(F_p) = 0`. That is Quillen's homotopy invariance for regular rings.
  Lavrenov–Sinchuk (arXiv:1909.02637, §1) state the isomorphism `K₂(A_ℓ, k[x₁..x_n]) ≅ K₂(A_ℓ, k)`
  as a *consequence* of the early stability theorem, and that consequence goes through the stable
  statement.
- Tulenbaev's proof of Thm 5.1 also uses Quillen's fundamental theorem
  `0 → K_q(k) → K_q(k[X]) ⊕ K_q(k[X⁻¹]) → K_q(k[X,X⁻¹])` for a field `k` (Cor 4.2, p.149), together
  with Suslin–Tulenbaev stabilization and van der Kallen's presentation of `St_r` (his refs [4],
  [5]).
- So the route "Tulenbaev, hence K₂ = ⊥ with no higher K-theory" is NOT elementary as it stands.
- A Steinberg-level `A¹`-invariance of `K₂(n, R[t])` for regular `R` containing a field does exist
  (Lavrenov–Sinchuk–Voronetsky, arXiv:2110.11087). It uses Lindel–Popescu, Nisnevich excision
  via pro-groups, Tulenbaev's `P¹`-glueing and the field case.

No reduction theorem is claimed in this module.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace Tulenbaev

open GroupApproximation.SteinbergGroup Polynomial

/-- **Quillen–Suslin local–global principle for `St_N`**, at ranks `N ≥ n₀`. If `g ∈ St_N(A[X])`
becomes constant in `St_N(A_𝔪[X])` for every maximal ideal `𝔪`, then `g` is constant. At
`n₀ = 5` this is Tulenbaev, Thm 2.1, in the form of the module docstring. -/
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

/-- Tulenbaev's local–global principle (Thm 2.1): the rank bound `r ≥ 5`, read at source. -/
abbrev StLocalGlobalStatement : Prop := StLocalGlobalStatementAt 5

/-- The coordinate `A[X] → A[T, T⁻¹]`, `X ↦ T`. -/
noncomputable def toLaurentPos (A : Type) [CommRing A] : A[X] →+* LaurentPolynomial A :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T 1)

/-- The coordinate `A[X] → A[T, T⁻¹]`, `X ↦ T⁻¹`, modelling `A[X⁻¹] → A[X, X⁻¹]`. -/
noncomputable def toLaurentNeg (A : Type) [CommRing A] : A[X] →+* LaurentPolynomial A :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))

/-- **Horrocks theorem for `K₂(N, -)`**, at ranks `N ≥ n₀`: the `K₂` form of
`TulenbaevHorrocks.StHorrocksStatementAt`. -/
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
