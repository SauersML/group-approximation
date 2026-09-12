import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity

/-!
# Sentence-level Leavitt calculations

Named forms of the coefficient calculations printed in the proof of
`prop:simple`.  These declarations expose the actual witnesses and identities
used by the manuscript instead of certifying only the final root-detection
endpoint.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u

variable {R : Type u} [Ring R]

/-- The exact factorization printed to show that `s₀t₁` is nonzero. -/
theorem manuscript_s0_t1_factorization [Nontrivial R]
    (L : LeavittFamily R) :
    (1 : R) = (L.t0 * L.s0) * (L.t1 * L.s1) ∧
      (L.t0 * L.s0) * (L.t1 * L.s1) =
        L.t0 * (L.s0 * L.t1) * L.s1 := by
  constructor
  · rw [L.t0_s0, L.t1_s1, one_mul]
  · noncomm_ring

/-- The middle Leavitt coefficient in the printed factorization is nonzero. -/
theorem manuscript_s0_mul_t1_ne_zero [Nontrivial R]
    (L : LeavittFamily R) : L.s0 * L.t1 ≠ 0 := by
  intro hzero
  have hfactor := manuscript_s0_t1_factorization L
  have honezero : (1 : R) = 0 := by
    calc
      1 = (L.t0 * L.s0) * (L.t1 * L.s1) := hfactor.1
      _ = L.t0 * (L.s0 * L.t1) * L.s1 := hfactor.2
      _ = 0 := by rw [hzero, mul_zero, zero_mul]
  exact one_ne_zero honezero

/-- The `w = 0` branch uses the two printed unit witnesses. -/
theorem manuscript_reversing_zero_product_zero [Nontrivial R] :
    (1 : R) * 0 * 1 = 0 ∧ (1 : R) * 1 ≠ 0 := by
  simp

/-- The exact witnesses `x=t₁c`, `y=ds₀` used in the nonzero branch. -/
theorem manuscript_reversing_zero_product_nonzero [Nontrivial R]
    (L : LeavittFamily R) {w c d : R} (hcwd : c * w * d = 1) :
    (L.t1 * c) * w * (d * L.s0) = 0 ∧
      (d * L.s0) * (L.t1 * c) ≠ 0 := by
  constructor
  · calc
      (L.t1 * c) * w * (d * L.s0) =
          L.t1 * (c * w * d) * L.s0 := by noncomm_ring
      _ = 0 := by rw [hcwd, mul_one, L.t1_s0]
  · intro hzero
    apply manuscript_s0_mul_t1_ne_zero L
    calc
      L.s0 * L.t1 = 1 * (L.s0 * L.t1) * 1 := by simp
      _ = (c * w * d) * (L.s0 * L.t1) * (c * w * d) := by rw [hcwd]
      _ = (c * w) * ((d * L.s0) * (L.t1 * c)) * (w * d) := by
        noncomm_ring
      _ = 0 := by rw [hzero, mul_zero, zero_mul]

/-- The four sandwich factorizations and the manuscript's displayed
definitions of `a,b` give the claimed coefficient separation. -/
theorem manuscript_coefficient_separation_explicit
    {r s cr dr ed fd es fs et ft x y : R}
    (hcr : cr * r * dr = 1) (hdf : ed * dr * fd = 1)
    (hsf : es * s * fs = 1) (htf : et * (cr * r) * ft = 1)
    (hxy : x * (et * fd) * y = 0) (hyx : y * x ≠ 0) :
    let a := fs * x * et * cr
    let b := dr * fd * y * es
    a * r * b = 0 ∧ b * s * a * r ≠ 0 := by
  dsimp only
  constructor
  · calc
      (fs * x * et * cr) * r * (dr * fd * y * es) =
          fs * x * et * (cr * r * dr) * fd * y * es := by noncomm_ring
      _ = fs * x * (et * fd) * y * es := by rw [hcr]; noncomm_ring
      _ = fs * (x * (et * fd) * y) * es := by noncomm_ring
      _ = 0 := by rw [hxy, mul_zero, zero_mul]
  · intro hzero
    apply hyx
    calc
      y * x = ed * ((dr * fd * y * es) * s *
          (fs * x * et * cr) * r) * ft := by
        symm
        calc
          ed * ((dr * fd * y * es) * s *
              (fs * x * et * cr) * r) * ft =
              (ed * dr * fd) * y * (es * s * fs) * x *
                (et * (cr * r) * ft) := by noncomm_ring
          _ = y * x := by rw [hdf, hsf, htf]; simp
      _ = 0 := by rw [hzero, mul_zero, zero_mul]

/-- A nontrivial subgroup contains a nonidentity ambient element, in the exact
form used at the start of the root-extraction proof. -/
theorem manuscript_choose_nonidentity_normal_element
    {G : Type*} [Group G] (N : Subgroup G) (hN : N ≠ ⊥) :
    ∃ g : G, g ∈ N ∧ g ≠ 1 := by
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
  exact ⟨g, g.property, fun h ↦ hg (Subtype.ext h)⟩

/-- The printed off-diagonal case selection: a matrix which is not diagonal
has a nonzero off-diagonal coefficient. -/
theorem manuscript_choose_nonzero_off_diagonal_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : elementaryGroup ι R)
    (hdiag : ¬ ∀ p q : ι, p ≠ q →
      ElementarySimplicity.elMat g p q = 0) :
    ∃ l i : ι, l ≠ i ∧ ElementarySimplicity.elMat g l i ≠ 0 := by
  push Not at hdiag
  exact hdiag

end OneSidedMFRadical
end Manuscript
end GroupApproximation
