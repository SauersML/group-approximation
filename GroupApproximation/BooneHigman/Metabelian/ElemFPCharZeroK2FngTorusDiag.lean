import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPStTorus
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Diagonal
import GroupApproximation.Meta.AxiomGuard

/-!
# The image of the torus element `H_ab(v)` in `E_I(R)` (lane `bh-met-92w`, part 1)

Lane `bh-met-92p` left out the concrete matrix lemma behind the torus residual
`czK2FngFour_TorusStatement`.  It is proved here, for every finite index type `I` and every
commutative ring `R`:

* `czK2FngTorus_H_eq`: `czStFourFP_H a b hab v = w_ab(v) w_ab(1)⁻¹` is the manuscript diagonal
  element `h_ab(v) = w_ab(v) w_ab(-1)` (because `w_ab(1)⁻¹ = w_ab(-1)`, `SteinbergWeyl.w_inv`).
* `czK2FngTorus_projection_H_val`: the image of `H_ab(v)` in `(Matrix I I R)ˣ` is
  `diag(…, v at a, …, v⁻¹ at b, …, 1 elsewhere)`
  (`SteinbergWeyl.manuscriptSentence_projectionDiagonalElement`).
* `czK2FngTorus_projection_H_commute`: any two torus elements have commuting images, since
  diagonal matrices over a commutative ring commute.

No hypothesis, no literature input.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

/-- `czStFourFP_w` is the manuscript Weyl element `SteinbergWeyl.w` (same defining word). -/
theorem czK2FngTorus_w_eq (a b : I) (hab : a ≠ b) (v : Rˣ) :
    czStFourFP_w a b hab v = SimpleKazhdanSofic.SkRows.SteinbergWeyl.w a b hab v :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_w_eq

/-- `H_ab(v) = w_ab(v) w_ab(1)⁻¹` is the manuscript diagonal element `h_ab(v)`. -/
theorem czK2FngTorus_H_eq (a b : I) (hab : a ≠ b) (v : Rˣ) :
    czStFourFP_H a b hab v = SimpleKazhdanSofic.SkRows.SteinbergWeyl.h a b hab v := by
  show czStFourFP_w a b hab v * (czStFourFP_w a b hab 1)⁻¹ =
    SimpleKazhdanSofic.SkRows.SteinbergWeyl.w a b hab v *
      SimpleKazhdanSofic.SkRows.SteinbergWeyl.w a b hab (-1)
  exact congrArg (czStFourFP_w a b hab v * ·)
    (SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_inv a b hab 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_H_eq

/-- **The matrix lemma.**  `projection (H_ab(v)) = diag(v at a, v⁻¹ at b, 1 elsewhere)`. -/
theorem czK2FngTorus_projection_H_val (a b : I) (hab : a ≠ b) (v : Rˣ) :
    ((projection (czStFourFP_H a b hab v) : (Matrix I I R)ˣ) : Matrix I I R) =
      Matrix.diagonal (fun k => if k = a then (v : R) else if k = b then ((v⁻¹ : Rˣ) : R)
        else 1) := by
  rw [czK2FngTorus_H_eq]
  exact SimpleKazhdanSofic.SkRows.SteinbergWeyl.manuscriptSentence_projectionDiagonalElement
    a b hab v

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_projection_H_val

/-- **Pairwise commuting images.**  The images of `H_ab(v)` and `H_cd(u)` in `E_I(R)`
commute (both are diagonal). -/
theorem czK2FngTorus_projection_H_commute (a b c d : I) (hab : a ≠ b) (hcd : c ≠ d)
    (v u : Rˣ) :
    projection (czStFourFP_H a b hab v) * projection (czStFourFP_H c d hcd u) =
      projection (czStFourFP_H c d hcd u) * projection (czStFourFP_H a b hab v) := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    czK2FngTorus_projection_H_val a b hab v, czK2FngTorus_projection_H_val c d hcd u,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ => mul_comm _ _)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_projection_H_commute

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
