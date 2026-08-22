import GroupApproximation.Sofic.CentralSignAnyUniverse
import GroupApproximation.Sofic.KazhdanTransportAnyUniverse
import GroupApproximation.Sofic.TransportVariantsAnyUniverse

/-!
# Exact subgroup forms of the manuscript transport criteria

The reusable transport theorems are stated for a homomorphism `ι : Γ → H`.
Several manuscript statements use the specialization in which the Kazhdan
group is literally a subgroup `L ≤ H`.  The declarations below make that
specialization explicit: their hypotheses and conclusions quantify over
ambient elements together with proofs of membership in `L`, and their proofs
apply the homomorphism forms to `L.subtype`.

-/

namespace GroupApproximation
namespace ManuscriptExactWrappers

open Matrix
open ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator commutatorElement

noncomputable section

universe u

/-! ## The subgroup form of ordinary transport -/

/-- Exact subgroup specialization of the manuscript's one-sided Kazhdan
transport theorem.  This is the statement obtained by taking `Γ = L` and
`ι = L.subtype`, but it is exposed in the manuscript's subgroup coordinates:
the compression, commutant hypothesis, and conclusion all quantify over
ambient elements belonging to `L`. -/
theorem manuscriptKazhdanTransportSubgroup :
    ∀ {H : Type u} [Group H]
      (L : Subgroup H) (_hT : HasKazhdanPropertyT.{u, u} L)
      (s : H) (_hs : ∀ gamma : H, gamma ∈ L → s * gamma * s⁻¹ ∈ L)
      (d : ℕ → ℕ) (_hd : ∀ n, 0 < d n)
      (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
      (_hU : ∀ g h : H, ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
        ‖(U n (g * h) : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ) -
          (U n g : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ) * U n h‖ ≤ epsilon)
      (x : ∀ n, Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ)
      (_hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
      (_hx : ∀ gamma : H, gamma ∈ L →
        KazhdanAsymptoticCommutant.NaturalHSCommutatorVanishing d U x gamma),
    ∀ gamma : H, gamma ∈ L →
      KazhdanAsymptoticCommutant.NaturalHSCommutatorVanishing d U (fun n ↦
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) gamma := by
  intro H _ L hT s hs d hd U hU x hbound hx gamma hgamma
  have hTComplex : HasKazhdanPropertyTComplex.{u, u} L :=
    hasKazhdanPropertyT_iff_textbook.mp hT
  have hcompresses : ∀ ell : L, ∃ delta : L,
      s * (ell : H) * s⁻¹ = (delta : H) := by
    intro ell
    exact ⟨⟨s * (ell : H) * s⁻¹, hs ell ell.property⟩, rfl⟩
  have hcommutant : ∀ ell : L,
      KazhdanAsymptoticCommutant.NaturalHSCommutatorVanishing
        d U x ((Subgroup.subtype L) ell) :=
    fun ell ↦ hx ell ell.property
  have hresult :=
    KazhdanAsymptoticCommutant.manuscriptKazhdanTransport_anyUniverse
      hTComplex (Subgroup.subtype L) s hcompresses d hd U hU x hbound
      hcommutant ⟨gamma, hgamma⟩
  exact hresult

/-! ## The subgroup form of the central-involution criterion -/

/-- Exact subgroup specialization of the central-involution criterion.  The
source homomorphism is the inclusion `L ↪ H`; in particular the marked element
`a`, the compression condition, and the centralizer condition are all stated
directly in the ambient group. -/
theorem manuscriptCentralSignCriterionSubgroup :
    ∀ {H : Type u} [Group H] [Countable H]
      (L : Subgroup H) (_hT : HasKazhdanPropertyT.{u, u} L)
      (t c : H)
      (_hcompresses : ∀ gamma : H, gamma ∈ L →
        t * gamma * t⁻¹ ∈ L)
      (_hcomm : ∀ gamma : H, gamma ∈ L → Commute c gamma)
      (a : H) (_ha : a ∈ L) (z : H)
      (_hz : z = ⁅t * c * t⁻¹, a⁆ ^ 2)
      (_hz_ne : z ≠ 1) (_hz_sq : z ^ 2 = 1)
      (_hz_central : ∀ g : H, Commute z g),
    (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∀ rho : H →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho z = 1) ∧
      ¬ IsCDEOperatorMF H := by
  intro H _ _ L hT t c hcompresses hcomm a ha z hz hz_ne hz_sq hz_central
  have hTComplex : HasKazhdanPropertyTComplex.{u, u} L :=
    hasKazhdanPropertyT_iff_textbook.mp hT
  have hcompressesSubtype : ∀ ell : L, ∃ delta : L,
      t * (ell : H) * t⁻¹ = (delta : H) := by
    intro ell
    exact ⟨⟨t * (ell : H) * t⁻¹, hcompresses ell ell.property⟩, rfl⟩
  have hcommSubtype : ∀ ell : L, Commute c ((ell : L) : H) :=
    fun ell ↦ hcomm ell ell.property
  exact KazhdanCompressionCore.manuscriptCentralSignCriterion_anyUniverse
    hTComplex (Subgroup.subtype L) t c hcompressesSubtype hcommSubtype
      ⟨a, ha⟩ z hz hz_ne hz_sq hz_central

/-! ## The subgroup form of weighted transport -/

/-- Thin subgroup specialization of weighted two-sided transport.  This is
`scaled_transport_both_anyUniverse` with source group `L`, homomorphism
`L.subtype`, and the harmless root `1`; no transport estimate is reproved. -/
theorem manuscriptWeightedTransportSubgroup :
    ∀ {H : Type u} [Group H]
      (B : OpAlmostRepresentation H) (weight : ℕ → ℝ)
      (_hweight : ∀ n, 0 ≤ weight n)
      (L : Subgroup H) (_hT : HasKazhdanPropertyT.{u, u} L)
      (s : H) (_hs : ∀ gamma : H, gamma ∈ L → s * gamma * s⁻¹ ∈ L)
      (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
      (_hx : IsScaledAsymptoticCommutantOf B weight (Subgroup.subtype L) x)
      (_hbound : IsScaledMassBounded B weight x),
    IsScaledAsymptoticCommutantOf B weight (Subgroup.subtype L)
        (KazhdanAsymptoticCommutant.adjointSequence B s x) ∧
      IsScaledAsymptoticCommutantOf B weight (Subgroup.subtype L)
        (KazhdanAsymptoticCommutant.coadjointSequence B s x) := by
  intro H _ B weight hweight L hT s hs x hx hbound
  let C : KazhdanCompressionCore L H := {
    iota := Subgroup.subtype L
    t := s
    c := 1
    kazhdan := hT
    compresses := by
      intro ell
      exact ⟨⟨s * (ell : H) * s⁻¹, hs ell ell.property⟩, rfl⟩
    comm_c := fun ell ↦ Commute.one_left ell
  }
  have hxC : IsScaledAsymptoticCommutant B weight C x := hx
  exact TransportVariantsAnyUniverse.scaled_transport_both_anyUniverse
    B weight hweight C x hxC hbound

end

end ManuscriptExactWrappers
end GroupApproximation
