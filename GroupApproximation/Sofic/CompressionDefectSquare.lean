import GroupApproximation.Sofic.MarkedCompressionInclusionData

/-!
# The marked compression word as a squared defect

For the commutator convention `[x,y] = x y x⁻¹ y⁻¹`, conjugating an
involution `d` by `a` gives the elementary identity

`[d, a d a⁻¹] = [d,a]²`.

Applied to `d = t c t⁻¹`, this identifies the marked compression word with
the square of one pointwise compression defect.  The normal closure itself
is defined once, in `KazhdanCompressionCore`; this file deliberately does
not introduce a marked-data duplicate.  The involution hypothesis on `c` is
explicit because
`MarkedCompressionInclusionData` deliberately records only the analytic data
and does not require `c` itself to have order two.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u

/-! ## The three steps of the printed proof

The manuscript proves `lem:square` by naming a factorization: it puts
`b = a₁ d a₁⁻¹`, observes `b² = a₁d²a₁⁻¹ = 1`, rewrites the pointwise defect
as `[d,a₁] = d(a₁da₁⁻¹) = db`, and then reads `(db)² = dbd⁻¹b⁻¹ = [d,b]` off
the two involutions.  Each of those three sentences is a lemma below, and the
cited declaration composes them in that order rather than discharging the
identity by normalization. -/

/-- If `d` is an involution, then centrality of
`[d, a d a⁻¹]` already forces that commutator to be an involution.  Thus the
square relator in the Kazhdan--Clifford presentation is redundant. -/
theorem markedCompressionWord_sq_eq_one_of_c_sq_of_central
    {G : Type*} [Group G] (t a c : G) (hc : c ^ 2 = 1)
    (hcentral : ∀ g : G, Commute (markedCompressionWord t a c) g) :
    markedCompressionWord t a c ^ 2 = 1 := by
  let d := t * c * t⁻¹
  let b := a * d * a⁻¹
  have hd : d ^ 2 = 1 := by
    dsimp [d]
    simp only [pow_two]
    have hcc : c * c = 1 := by simpa [pow_two] using hc
    calc
      (t * c * t⁻¹) * (t * c * t⁻¹) =
          t * (c * c) * t⁻¹ := by group
      _ = 1 := by rw [hcc]; group
  have hb : b ^ 2 = 1 := by
    dsimp [b]
    simp only [pow_two]
    have hdd : d * d = 1 := by simpa [pow_two] using hd
    calc
      (a * d * a⁻¹) * (a * d * a⁻¹) = a * (d * d) * a⁻¹ := by group
      _ = 1 := by rw [hdd]; group
  have hdInv : d⁻¹ = d := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hd
  have hbInv : b⁻¹ = b := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hb
  have hdd : d * d = 1 := by simpa [pow_two] using hd
  have hword : markedCompressionWord t a c = d * b * d * b := by
    simp [markedCompressionWord, d, b, commutatorElement_def, hdInv, hbInv]
  have hconjInv :
      d * markedCompressionWord t a c * d⁻¹ =
        (markedCompressionWord t a c)⁻¹ := by
    rw [hword, hdInv]
    simp only [_root_.mul_inv_rev, hdInv, hbInv]
    calc
      d * (d * b * d * b) * d = (d * d) * b * d * b * d := by group
      _ = b * (d * (b * d)) := by
        rw [hdd]
        simp only [one_mul, mul_assoc]
  have hconjFix :
      d * markedCompressionWord t a c * d⁻¹ =
        markedCompressionWord t a c := by
    calc
      d * markedCompressionWord t a c * d⁻¹ =
          markedCompressionWord t a c * d * d⁻¹ := by
            rw [(hcentral d).eq]
      _ = markedCompressionWord t a c := by simp
  have hinv : (markedCompressionWord t a c)⁻¹ =
      markedCompressionWord t a c := hconjInv.symm.trans hconjFix
  have hcancel := inv_mul_cancel (markedCompressionWord t a c)
  rw [hinv] at hcancel
  simpa [pow_two] using hcancel

end GroupApproximation
