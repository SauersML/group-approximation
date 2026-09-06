import GroupApproximation.CharClass.LIXVBundle
import GroupApproximation.CharClass.SliceVFlat

/-!
# The lines of `V` over the projective base

`cc-lix-odd`'s bundle lives over `baseY dd`, because `H` reads only the projective
coordinate, while their family of lines is written over `baseM dd`.  The lines do
not see the sphere factor either, so they descend, and this file carries the
decomposition down and then flattens it.

The descent is `VmatY_eq` read at a constant sphere coordinate, which is the same
device `continuous_VmatY` uses, so the relation between the two forms stays
definitional.

What is **not** here, and is the only thing between this and the splitting
principle: each line is a continuous projection-valued map, which the splitting
principle needs because it consumes the summands as bundles and not as matrix
families.  The traces are `cc-lix-odd`'s; the other two fields are theirs by
vocabulary and are not supplied yet.

## Main declarations

* `vLineY` — the lines over the projective base.
* `VmatY_eq_sum_lines` — the decomposition there.
* `vLineYFlat`, `VmatY_eq_sum_rangeY`, `trace_vLineYFlat` — flattened to a range.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

noncomputable section

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- The lines of `V`, over the projective base.  They do not see the sphere
coordinate, so reading them at a constant one loses nothing. -/
def vLineY (b : Fin 3 ⊕ HBlk dd) (y : baseY dd) : Matrix (VIdx dd) (VIdx dd) ℂ :=
  vLine b ((negEThree, y) : baseM dd)

theorem trace_vLineY (b : Fin 3 ⊕ HBlk dd) (y : baseY dd) :
    Matrix.trace (vLineY b y) = 1 := trace_vLine b _

/-- **The decomposition over the projective base.** -/
theorem VmatY_eq_sum_lines (y : baseY dd) :
    VmatY y = ∑ b : Fin 3 ⊕ HBlk dd, vLineY b y := by
  rw [show VmatY y = Vmat ((negEThree, y) : baseM dd) from VmatY_eq ((negEThree, y) : baseM dd)]
  exact Vmat_eq_sum_lines _

/-- The lines over the projective base, indexed by a natural and zero off the
range. -/
def vLineYFlat (dd : Fin ℓ → ℕ) (y : baseY dd) (l : ℕ) :
    Matrix (VIdx dd) (VIdx dd) ℂ :=
  if h : l < lixRank dd then vLineY ((vIndexEquiv dd).symm ⟨l, h⟩) y else 0

theorem vLineYFlat_apply_equiv (dd : Fin ℓ → ℕ) (y : baseY dd) (b : Fin 3 ⊕ HBlk dd) :
    vLineYFlat dd y ((vIndexEquiv dd b : Fin (lixRank dd)) : ℕ) = vLineY b y := by
  have hlt : ((vIndexEquiv dd b : Fin (lixRank dd)) : ℕ) < lixRank dd :=
    (vIndexEquiv dd b).isLt
  have hb : (vIndexEquiv dd).symm ⟨((vIndexEquiv dd b : Fin (lixRank dd)) : ℕ), hlt⟩ = b := by
    rw [Fin.eta]
    exact (vIndexEquiv dd).symm_apply_apply b
  rw [vLineYFlat, dif_pos hlt, hb]

/-- **The decomposition over the projective base, over a flat range.** -/
theorem VmatY_eq_sum_rangeY (y : baseY dd) :
    VmatY y = ∑ l ∈ Finset.range (lixRank dd), vLineYFlat dd y l := by
  rw [sum_range_of_equiv (lixRank dd) (vIndexEquiv dd) (fun b => vLineY b y)
    (vLineYFlat dd y) (vLineYFlat_apply_equiv dd y)]
  exact VmatY_eq_sum_lines y

theorem trace_vLineYFlat (y : baseY dd) {l : ℕ} (hl : l < lixRank dd) :
    Matrix.trace (vLineYFlat dd y l) = 1 := by
  rw [vLineYFlat, dif_pos hl]
  exact trace_vLineY _ y

end

end GroupApproximation.CharClass
