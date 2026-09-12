import GroupApproximation.Sofic.MarkedCompressionInclusionData
import Mathlib.GroupTheory.Commutator.Basic

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

/-- `b = a d a⁻¹` is again an involution: `b² = a d² a⁻¹`.  This is the
manuscript's first sentence, "so `b² = a₁d²a₁⁻¹ = 1`". -/
theorem conj_sq_eq_one {G : Type*} [Group G] (d a : G) (hd : d ^ 2 = 1) :
    (a * d * a⁻¹) ^ 2 = 1 := by
  calc (a * d * a⁻¹) ^ 2
      = a * d * (a⁻¹ * a) * d * a⁻¹ := by
        rw [pow_two]
        simp only [mul_assoc]
    _ = a * d ^ 2 * a⁻¹ := by
        rw [inv_mul_cancel, mul_one, pow_two]
        simp only [mul_assoc]
    _ = 1 := by rw [hd, mul_one, mul_inv_cancel]

/-- **The printed factorization of the pointwise defect.**  For an involution
`d`, the commutator `[d,a] = d a d⁻¹ a⁻¹` collapses to `d` times the conjugate
`a d a⁻¹`: the manuscript's `[d,a₁] = d(a₁da₁⁻¹) = db`. -/
theorem commutator_eq_mul_conj {G : Type*} [Group G] (d a : G)
    (hd : d ^ 2 = 1) : ⁅d, a⁆ = d * (a * d * a⁻¹) := by
  have hd_inv : d⁻¹ = d := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hd
  rw [commutatorElement_def, hd_inv]
  group

/-- **The printed reading of the square.**  A product of two involutions
squares to their commutator: `(db)² = dbdb = dbd⁻¹b⁻¹ = [d,b]`. -/
theorem sq_mul_eq_commutator {G : Type*} [Group G] (d b : G)
    (hd : d ^ 2 = 1) (hb : b ^ 2 = 1) : (d * b) ^ 2 = ⁅d, b⁆ := by
  have hd_inv : d⁻¹ = d := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hd
  have hb_inv : b⁻¹ = b := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hb
  rw [commutatorElement_def, hd_inv, hb_inv, pow_two]
  group

/-- If `d` is an involution, its commutator with its `a`-conjugate is the
square of the pointwise defect `[d,a]`.  This is the group identity used by
the manuscript's `lem:square`.

The proof is the printed one and travels the printed road in the printed
direction.  The manuscript starts at `[d,a₁]²` and works down to `[d,b]`, so
the chain below is set up by `Eq.symm` to run that way rather than back from
the goal's left-hand side: put `b = a d a⁻¹`, which is an involution by
`conj_sq_eq_one`; the square of the pointwise defect is `(db)²` by
`commutator_eq_mul_conj`; and `(db)²` is `[d,b]` by `sq_mul_eq_commutator`.
The three substeps are therefore consumed in the order the manuscript
establishes them. -/
theorem commutator_conjugate_eq_commutator_sq_of_sq_eq_one :
    ∀ {G : Type*} [Group G] (d a : G), d ^ 2 = 1 →
    ⁅d, a * d * a⁻¹⁆ = ⁅d, a⁆ ^ 2 := by
  intro G _ d a hd
  have hb : (a * d * a⁻¹) ^ 2 = 1 := conj_sq_eq_one d a hd
  refine Eq.symm ?_
  calc ⁅d, a⁆ ^ 2 = (d * (a * d * a⁻¹)) ^ 2 := by
        rw [commutator_eq_mul_conj d a hd]
    _ = ⁅d, a * d * a⁻¹⁆ := sq_mul_eq_commutator d (a * d * a⁻¹) hd hb

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

namespace MarkedCompressionInclusionData

variable {Gamma : Type} {E : Type u} [Group Gamma] [Group E]

/-- Conjugating an involution preserves its square relation. -/
theorem transported_sq_eq_one (D : MarkedCompressionInclusionData Gamma E)
    (hc : D.c ^ 2 = 1) :
    (D.t * D.c * D.t⁻¹) ^ 2 = 1 := by
  calc
    (D.t * D.c * D.t⁻¹) ^ 2 = D.t * D.c ^ 2 * D.t⁻¹ := by
      simp only [pow_two]
      group
    _ = 1 := by rw [hc]; group

/-- For involutive `c`, the marked compression word is exactly the square of
the distinguished pointwise compression defect. -/
theorem word_eq_compressionDefect_sq
    (D : MarkedCompressionInclusionData Gamma E) (hc : D.c ^ 2 = 1) :
    D.word = ⁅D.t * D.c * D.t⁻¹, D.iota D.a⁆ ^ 2 := by
  rw [word, markedCompressionWord]
  exact commutator_conjugate_eq_commutator_sq_of_sq_eq_one
    (D.t * D.c * D.t⁻¹) (D.iota D.a) (D.transported_sq_eq_one hc)

end MarkedCompressionInclusionData

end GroupApproximation
