import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendBoundedStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Polar unitary, lane `nm-tww-17b`: polarization

Step 1 of Lance, Thm. 3.5. If `⟨Sx, Sx⟩ = ⟨Tx, Tx⟩` for every `x`, then
`⟨Sx, Sy⟩ = ⟨Tx, Ty⟩` for all `x`, `y`.

Route. `q x y = ⟨Sx, Sy⟩ - ⟨Tx, Ty⟩` is sesquilinear and vanishes on the diagonal.
Expanding `q (x + y) (x + y) = 0` gives `q x y + q y x = 0`. Expanding
`q (x + i y) (x + i y) = 0` gives `i q x y - i q y x = 0`. Together these give
`2i q x y = 0`, so `q x y = 0`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule

universe v

/-- **Polarization**: a sesquilinear form that vanishes on the diagonal is zero. -/
theorem sesq_eq_zero_of_diag {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] (q : M → M → N) (hal : ∀ x y z, q (x + y) z = q x z + q y z)
    (har : ∀ x y z, q x (y + z) = q x y + q x z)
    (hsl : ∀ (c : ℂ) x y, q (c • x) y = (starRingEnd ℂ) c • q x y)
    (hsr : ∀ (c : ℂ) x y, q x (c • y) = c • q x y) (hq : ∀ x, q x x = 0) (x y : M) :
    q x y = 0 := by
  have h1 : q x y + q y x = 0 := by
    have h := hq (x + y)
    rw [hal, har, har, hq x, hq y, zero_add, add_zero] at h
    exact h
  have h2 : Complex.I • q x y + (starRingEnd ℂ) Complex.I • q y x = 0 := by
    have h := hq (x + Complex.I • y)
    rw [hal, har, har, hsr, hsr, hsl, hsl, hq x, hq y, smul_zero, smul_zero, zero_add,
      add_zero] at h
    exact h
  have hb : q y x = -q x y := eq_neg_of_add_eq_zero_right h1
  rw [hb, Complex.conj_I, smul_neg, neg_smul, neg_neg] at h2
  have h3 : (2 * Complex.I) • q x y = 0 := by
    rw [← smul_smul, two_smul ℂ, h2]
  have hc : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  calc q x y = (2 * Complex.I)⁻¹ • (2 * Complex.I) • q x y := (inv_smul_smul₀ hc _).symm
    _ = 0 := by rw [h3, smul_zero]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.sesq_eq_zero_of_diag

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Diagonal agreement of inner products gives full agreement.** -/
theorem inner_eq_inner_of_diag {E F G : CStarModule.{v, v} B} (S : Adjointable E F)
    (T : Adjointable E G)
    (hS : ∀ x : E.carrier, F.inner (S.toFun x) (S.toFun x) = G.inner (T.toFun x) (T.toFun x))
    (x y : E.carrier) :
    F.inner (S.toFun x) (S.toFun y) = G.inner (T.toFun x) (T.toFun y) := by
  let q : E.carrier → E.carrier → B := fun a b =>
    F.inner (S.toFun a) (S.toFun b) - G.inner (T.toFun a) (T.toFun b)
  have hal : ∀ a b c, q (a + b) c = q a c + q b c := by
    intro a b c
    show F.inner (S.toFun (a + b)) (S.toFun c) - G.inner (T.toFun (a + b)) (T.toFun c)
      = (F.inner (S.toFun a) (S.toFun c) - G.inner (T.toFun a) (T.toFun c))
        + (F.inner (S.toFun b) (S.toFun c) - G.inner (T.toFun b) (T.toFun c))
    rw [S.map_add, T.map_add, F.inner_add_left, G.inner_add_left]
    abel
  have har : ∀ a b c, q a (b + c) = q a b + q a c := by
    intro a b c
    show F.inner (S.toFun a) (S.toFun (b + c)) - G.inner (T.toFun a) (T.toFun (b + c))
      = (F.inner (S.toFun a) (S.toFun b) - G.inner (T.toFun a) (T.toFun b))
        + (F.inner (S.toFun a) (S.toFun c) - G.inner (T.toFun a) (T.toFun c))
    rw [S.map_add, T.map_add, F.inner_add_right, G.inner_add_right]
    abel
  have hsl : ∀ (c : ℂ) a b, q (c • a) b = (starRingEnd ℂ) c • q a b := by
    intro c a b
    show F.inner (S.toFun (c • a)) (S.toFun b) - G.inner (T.toFun (c • a)) (T.toFun b)
      = (starRingEnd ℂ) c • (F.inner (S.toFun a) (S.toFun b) - G.inner (T.toFun a) (T.toFun b))
    rw [S.map_smul, T.map_smul, F.inner_smul_left, G.inner_smul_left, smul_sub]
  have hsr : ∀ (c : ℂ) a b, q a (c • b) = c • q a b := by
    intro c a b
    show F.inner (S.toFun a) (S.toFun (c • b)) - G.inner (T.toFun a) (T.toFun (c • b))
      = c • (F.inner (S.toFun a) (S.toFun b) - G.inner (T.toFun a) (T.toFun b))
    rw [S.map_smul, T.map_smul, F.inner_smul_right, G.inner_smul_right, smul_sub]
  have hq : ∀ a, q a a = 0 := fun a => sub_eq_zero.mpr (hS a)
  exact sub_eq_zero.mp (sesq_eq_zero_of_diag q hal har hsl hsr hq x y)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.inner_eq_inner_of_diag

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab
