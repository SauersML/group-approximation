import GroupApproximation.Sofic.ScaledKazhdanTransport

/-!
# The scaled asymptotic commutant is detected on a generating set

**Manuscript reference.** `non_mf_groups_exist.tex`, Theorem
`thm:transport-variants`(1) and Step 6 of the proof sketch of
`thm:collapse`.  The printed Step 6 checks that the compressed primitive is
"almost fixed by every `a ∈ S`", `S` the Kazhdan generating set; the
formalized hypothesis of the transport theorem
(`ScaledKazhdanTransport.IsScaledAsymptoticCommutantOf`) quantifies over
**all** of `Γ`.  The manuscript never remarks on the difference, because at
the level of the ultraproduct the two are the same statement: the elements
at which a mass-bounded sequence scaled-commutes form a *subgroup* of the
ambient group.

This module proves exactly that, and derives the generating-set criterion.
It is the second of the two ingredients that
`notes/COLLAPSE_STEP_AUDIT.md` finding R1, route (b), needs; the first is the
tolerance diagonalization of
`Sofic.CollapseTransportDiagonalization`.

The three closure proofs are the group-law bookkeeping already proved in
`Sofic.ScaledKazhdanTransport` (`scaled_adjointSequence_one`,
`scaled_adjointSequence_mul`, `scaled_adjointSequence_inv`), assembled: the
multiplicative defect of the almost representation is scaled-mass null
against a mass-bounded sequence, so the adjoint action is a genuine action
up to scaled-mass-null error.
-/

namespace GroupApproximation
namespace CollapseTransportDiagonalizationCommutant

open Matrix KazhdanAsymptoticCommutant ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]

/-- **The scaled commutant of a fixed mass-bounded sequence is a
subgroup.**  `g` belongs when the adjoint displacement `x - U_g x U_g*` is
scaled-mass null at the weight `w`. -/
def scaledCommutingSubgroup (B : OpAlmostRepresentation E) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x) : Subgroup E where
  carrier := {g | ScaledMassVanishing B w
    (fun n ↦ x n - adjointSequence B g x n)}
  one_mem' := by
    show ScaledMassVanishing B w (fun n ↦ x n - adjointSequence B 1 x n)
    exact (scaled_adjointSequence_one hw x hbound).sub_symm
  mul_mem' := by
    intro g h hg hh
    have hg' : ScaledMassVanishing B w
        (fun n ↦ x n - adjointSequence B g x n) := hg
    have hh' : ScaledMassVanishing B w
        (fun n ↦ x n - adjointSequence B h x n) := hh
    have hconj := hh'.unitary_conjugate (fun n ↦ B.map n g)
    have hmul := scaled_adjointSequence_mul hw g h x hbound
    show ScaledMassVanishing B w
      (fun n ↦ x n - adjointSequence B (g * h) x n)
    refine ((hg'.add hconj).add hmul.neg).congr fun n ↦ ?_
    simp only [adjointSequence]
    noncomm_ring
  inv_mem' := by
    intro g hg
    have hg' : ScaledMassVanishing B w
        (fun n ↦ x n - adjointSequence B g x n) := hg
    -- the reverse adjoint displacement is null too
    have hrev : ScaledMassVanishing B w
        (fun n ↦ x n - coadjointSequence B g x n) := by
      have hconj := hg'.neg.unitary_conjugate (fun n ↦
        ⟨(B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ,
          KazhdanCompressorCorner.conjTranspose_mem_unitaryGroup
            (B.map n g).2⟩)
      refine hconj.congr fun n ↦ ?_
      have hUU : (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) = 1 :=
        Unitary.star_mul_self_of_mem (B.map n g).2
      show (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            (-(x n - (B.map n g : Matrix (B.model n) (B.model n) ℂ) * x n *
              (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ)) *
            ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ =
          x n - (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ)
      rw [Matrix.conjTranspose_conjTranspose]
      have hexpand : (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            (-(x n - (B.map n g : Matrix (B.model n) (B.model n) ℂ) * x n *
              (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ)) *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ) =
          ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
              (B.map n g : Matrix (B.model n) (B.model n) ℂ)) * x n *
              ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
                (B.map n g : Matrix (B.model n) (B.model n) ℂ)) -
            (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
              (B.map n g : Matrix (B.model n) (B.model n) ℂ) := by
        noncomm_ring
      rw [hexpand, hUU, one_mul, mul_one]
    have hinv := scaled_adjointSequence_inv hw g x hbound
    show ScaledMassVanishing B w
      (fun n ↦ x n - adjointSequence B g⁻¹ x n)
    refine (hrev.add hinv.neg).congr fun n ↦ ?_
    simp only [adjointSequence, coadjointSequence]
    abel

/-- Membership in the scaled commutant subgroup is the displacement
condition, definitionally. -/
theorem mem_scaledCommutingSubgroup {B : OpAlmostRepresentation E}
    {w : ℕ → ℝ} {hw : ∀ n, 0 ≤ w n}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    {hbound : IsScaledMassBounded B w x} {g : E} :
    g ∈ scaledCommutingSubgroup B w hw x hbound ↔
      ScaledMassVanishing B w (fun n ↦
        x n - (B.map n g : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
  Iff.rfl

/-- **The generating-set criterion for the scaled asymptotic commutant.**
A mass-bounded sequence whose adjoint displacement is scaled-mass null at
every element of a generating set of `Γ` lies in the whole scaled asymptotic
commutant of `ι`.  This is what lets Step 6 of `thm:collapse` — which only
checks the Kazhdan generators `a ∈ S` — feed
`ScaledKazhdanTransport.scaled_transport_both`, whose hypothesis is stated
over all of `Γ`. -/
theorem isScaledAsymptoticCommutantOf_of_generating
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* E) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x)
    (hS : ∀ a ∈ S, ScaledMassVanishing B w (fun n ↦
      x n - (B.map n (iota a) : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n (iota a) : Matrix (B.model n) (B.model n) ℂ)ᴴ)) :
    IsScaledAsymptoticCommutantOf B w iota x := by
  intro γ
  have hle : Subgroup.closure (S : Set Γ) ≤
      (scaledCommutingSubgroup B w hw x hbound).comap iota := by
    rw [Subgroup.closure_le]
    intro a ha
    exact hS a (Finset.mem_coe.mp ha)
  have hmem : γ ∈ Subgroup.closure (S : Set Γ) := by
    rw [hgen]
    exact Subgroup.mem_top γ
  exact hle hmem

end CollapseTransportDiagonalizationCommutant
end GroupApproximation
