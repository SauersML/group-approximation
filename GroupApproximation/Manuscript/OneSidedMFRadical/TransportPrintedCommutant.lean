import GroupApproximation.Manuscript.OneSidedMFRadical.TransportCommutantEquality
import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted
import GroupApproximation.Analysis.AmenableTraceHyperlinear

/-!
# The printed `𝒞₂(V, L)`, the Hilbert--Schmidt asymptotic commutant

`non_mf_groups_exist.tex`, the paragraph before Lemma `lem:stable-finite`:

> For `L ≤ G`, let
> `𝒞₂(V,L) = { (x_n) | sup_n ‖x_n‖₂ < ∞, ‖V_n(ℓ)x_n − x_nV_n(ℓ)‖₂ → 0 (ℓ ∈ L) }`
> be the Hilbert--Schmidt asymptotic commutant of `V(L)`.  Coordinatewise
> conjugation by `V_n(g)` defines a bijection, denoted `Ad(V(g))`, of the
> Hilbert--Schmidt bounded matrix sequences.

The bound is now the *Hilbert--Schmidt* one, `sup_n ‖x_n‖₂ < ∞`; the printed
definition no longer asks for a uniform operator-norm bound.  The existing
`Manuscript/OneSidedMFRadical/TransportCommutantEquality.lean` carries the
older reading, `boundedHSCommutant`, whose boundedness clause is
`KazhdanAsymptoticCommutant.IsUniformlyBounded` — an operator-norm bound.
Since `‖a‖₂ ≤ ‖a‖`, the old set is contained in the printed one
(`boundedHSCommutant_subset` below), so the printed statement is stronger,
and that module is left untouched.

This file is the definition and its immediate consequences, with the printed
theorem stated as the closed proposition `PrintedTransportHS`.  Nothing here
proves it.

Two readings of "asymptotically commutes" appear in the manuscript: the
printed commutator `V_n(ℓ)x_n − x_nV_n(ℓ)` here, and the conjugation
displacement `V_n(ℓ)x_nV_n(ℓ)* − x_n` used in the proof.  They are the same
condition — `(V x − x V)V* = V x V* − x` and `‖·‖₂` is right unitarily
invariant — and `isHSAsymptoticallyCentral_iff_adjointSequence` is that
identification.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TransportPrintedCommutant

open Filter Matrix Topology
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G]

/-! ## The printed definition -/

/-- **The printed `sup_n ‖x_n‖₂ < ∞`.** -/
def IsHSBounded (B : OpAlmostRepresentation G)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∃ C : ℝ, ∀ n, hsNorm (B.model n) (x n) ≤ C

/-- **The printed `‖V_n(ℓ)x_n − x_nV_n(ℓ)‖₂ → 0` for `ℓ ∈ L`.** -/
def IsHSAsymptoticallyCentral (B : OpAlmostRepresentation G) (L : Subgroup G)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∀ ell ∈ L, Tendsto (fun n ↦ hsNorm (B.model n)
    ((B.map n ell : Matrix (B.model n) (B.model n) ℂ) * x n
      - x n * (B.map n ell : Matrix (B.model n) (B.model n) ℂ)))
    atTop (nhds 0)

/-- **The printed `𝒞₂(V, L)`.** -/
def printedCTwo (B : OpAlmostRepresentation G) (L : Subgroup G) :
    Set (∀ n, Matrix (B.model n) (B.model n) ℂ) :=
  {x | IsHSBounded B x ∧ IsHSAsymptoticallyCentral B L x}

/-! ## The two readings of "asymptotically commutes" -/

/-- `(V x − x V)V* = V x V* − x`, so the printed commutator and the
conjugation displacement have the same Hilbert--Schmidt norm. -/
theorem hsNorm_commutator_eq_hsNorm_conj (B : OpAlmostRepresentation G)
    (n : ℕ) (ell : G) (a : Matrix (B.model n) (B.model n) ℂ) :
    hsNorm (B.model n)
        ((B.map n ell : Matrix (B.model n) (B.model n) ℂ) * a
          - a * (B.map n ell : Matrix (B.model n) (B.model n) ℂ))
      = hsNorm (B.model n)
          ((B.map n ell : Matrix (B.model n) (B.model n) ℂ) * a *
            (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ - a) := by
  have hV : (B.map n ell : Matrix (B.model n) (B.model n) ℂ) ∈
      Matrix.unitaryGroup (B.model n) ℂ := (B.map n ell).2
  have hVVstar : (B.map n ell : Matrix (B.model n) (B.model n) ℂ) *
      (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem hV
  have hfac : ((B.map n ell : Matrix (B.model n) (B.model n) ℂ) * a
        - a * (B.map n ell : Matrix (B.model n) (B.model n) ℂ)) *
        (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ
      = (B.map n ell : Matrix (B.model n) (B.model n) ℂ) * a *
          (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ - a := by
    calc ((B.map n ell : Matrix (B.model n) (B.model n) ℂ) * a
          - a * (B.map n ell : Matrix (B.model n) (B.model n) ℂ)) *
          (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ
        = (B.map n ell : Matrix (B.model n) (B.model n) ℂ) * a *
            (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ
          - a * ((B.map n ell : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
          noncomm_ring
      _ = _ := by rw [hVVstar, Matrix.mul_one]
  rw [← hfac]
  exact (PrelimNotation.hsNorm_mul_right (B.model n)
    (conjTranspose_mem_unitaryGroup hV) _).symm

/-- **The printed condition, in the conjugation-displacement form the proof
uses.** -/
theorem isHSAsymptoticallyCentral_iff_adjointSequence
    (B : OpAlmostRepresentation G) (L : Subgroup G)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) :
    IsHSAsymptoticallyCentral B L x ↔
      ∀ ell ∈ L, Tendsto (fun n ↦ hsNorm (B.model n)
        (adjointSequence B ell x n - x n)) atTop (nhds 0) := by
  constructor
  · intro h ell hell
    refine (h ell hell).congr fun n ↦ ?_
    exact hsNorm_commutator_eq_hsNorm_conj B n ell (x n)
  · intro h ell hell
    refine (h ell hell).congr fun n ↦ ?_
    exact (hsNorm_commutator_eq_hsNorm_conj B n ell (x n)).symm

/-! ## Closure properties -/

/-- Coordinatewise conjugation preserves the printed bound: `‖·‖₂` is
unitarily invariant on both sides. -/
theorem isHSBounded_adjointSequence {B : OpAlmostRepresentation G} {g : G}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ} (hx : IsHSBounded B x) :
    IsHSBounded B (adjointSequence B g x) := by
  obtain ⟨C, hC⟩ := hx
  refine ⟨C, fun n ↦ ?_⟩
  have hV : (B.map n g : Matrix (B.model n) (B.model n) ℂ) ∈
      Matrix.unitaryGroup (B.model n) ℂ := (B.map n g).2
  have heq : hsNorm (B.model n) (adjointSequence B g x n)
      = hsNorm (B.model n) (x n) :=
    PrelimNotation.hsNorm_unitary_mul_mul (B.model n) hV
      (conjTranspose_mem_unitaryGroup hV) (x n)
  rw [heq]
  exact hC n

/-- The same for the inverse conjugation. -/
theorem isHSBounded_coadjointSequence {B : OpAlmostRepresentation G} {g : G}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ} (hx : IsHSBounded B x) :
    IsHSBounded B (coadjointSequence B g x) := by
  obtain ⟨C, hC⟩ := hx
  refine ⟨C, fun n ↦ ?_⟩
  have hV : (B.map n g : Matrix (B.model n) (B.model n) ℂ) ∈
      Matrix.unitaryGroup (B.model n) ℂ := (B.map n g).2
  have heq : hsNorm (B.model n) (coadjointSequence B g x n)
      = hsNorm (B.model n) (x n) :=
    PrelimNotation.hsNorm_unitary_mul_mul (B.model n)
      (conjTranspose_mem_unitaryGroup hV) hV (x n)
  rw [heq]
  exact hC n

/-- **The old reading is contained in the printed one.**  An operator-norm
bound is a Hilbert--Schmidt bound, because `‖a‖₂ ≤ ‖a‖`. -/
theorem isHSBounded_of_isUniformlyBounded {B : OpAlmostRepresentation G}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsUniformlyBounded B x) : IsHSBounded B x := by
  obtain ⟨M, -, hM⟩ := hx
  exact ⟨M, fun n ↦ (PrelimNotation.hsNorm_le_l2_opNorm (B.model n) (x n)).trans
    (hM n)⟩

/-- A Hilbert--Schmidt-squared vanishing sequence has vanishing
Hilbert--Schmidt norm. -/
theorem tendsto_hsNorm_of_hsSqVanishing {B : OpAlmostRepresentation G}
    {y : ∀ n, Matrix (B.model n) (B.model n) ℂ} (h : HSSqVanishing B y) :
    Tendsto (fun n ↦ hsNorm (B.model n) (y n)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N, hN⟩ := h (eps ^ 2 / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg (B.model n) (y n))]
  have h1 : hsNorm (B.model n) (y n) ^ 2 ≤ eps ^ 2 / 2 := by
    rw [TracialUltraproduct.sq_hsNorm]
    exact hN n hn
  nlinarith [hsNorm_nonneg (B.model n) (y n), heps]

/-- **The old operator-norm reading sits inside the printed one.** -/
theorem boundedHSCommutant_subset (B : OpAlmostRepresentation G)
    (L : Subgroup G) : boundedHSCommutant B L ⊆ printedCTwo B L := by
  rintro x ⟨hb, hc⟩
  refine ⟨isHSBounded_of_isUniformlyBounded hb, ?_⟩
  rw [isHSAsymptoticallyCentral_iff_adjointSequence]
  intro ell hell
  refine (tendsto_hsNorm_of_hsSqVanishing (hc ⟨ell, hell⟩)).congr fun n ↦ ?_
  exact AmenableTraceHyperlinear.hsNorm_sub_comm (B.model n) _ _

/-! ## Two containments give the printed equality -/

/-- The printed `Ad(V(g))` is a bijection of the Hilbert--Schmidt bounded
sequences, so preserving `𝒞₂(V,L)` in both directions gives the printed
equality of sets. -/
theorem image_eq_of_preserves (B : OpAlmostRepresentation G) (L : Subgroup G)
    (u : G)
    (hfwd : ∀ x ∈ printedCTwo B L, adjointSequence B u x ∈ printedCTwo B L)
    (hbwd : ∀ x ∈ printedCTwo B L, coadjointSequence B u x ∈ printedCTwo B L) :
    adjointSequence B u '' printedCTwo B L = printedCTwo B L := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨x, hx, rfl⟩
    exact hfwd x hx
  · intro y hy
    exact ⟨coadjointSequence B u y, hbwd y hy,
      adjointSequence_coadjointSequence B u y⟩

/-! ## The printed theorem -/

/-- **Theorem `thm:transport`, at the printed definition of `𝒞₂`.**

> Let `L ≤ G` have property (T), and let `u ∈ G` satisfy `uLu⁻¹ ≤ L`.  Let
> `(V_n)` be an operator norm asymptotic representation of `G`.  Then
> `Ad(V(u))(𝒞₂(V,L)) = 𝒞₂(V,L)`.

`compressionSet L` is the printed `uLu⁻¹ ≤ L`.  The difference from
`OneSidedKazhdanTransportCommutantEquality` is `printedCTwo` in place of
`boundedHSCommutant`: the printed bound is the Hilbert--Schmidt one, so this
is a statement about a larger set. -/
def PrintedTransportHS : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} L →
    ∀ (B : OpAlmostRepresentation G) (u : G), u ∈ compressionSet L →
      adjointSequence B u '' printedCTwo B L = printedCTwo B L

end

end TransportPrintedCommutant
end OneSidedMFRadical
end Manuscript
end GroupApproximation
