import GroupApproximation.Analysis.CollapseCompressionBundle

/-!
# The printed contradiction, with membership only where the print has it

Proof-ledger rows `CO.04`, `CO.20`, `CO.21`, `CO.21b`.
`CollapseCompressionBundle.collapse_contradiction_printed` takes the
displacement family as `d : H → rankIdeal`, valued in the ideal on the whole
ambient group.  The printed proof of `thm:projection-collapse` in
`non_mf_groups_exist.tex` never has that much: `d_g ∈ 𝓘_q` is proved for
`g ∈ L` — the induction of `CollapseDisplacementIdeal` runs over the subgroup
the generators produce — and the displacement at the compressor `s` itself is
not an ideal element and is never used.  Wiring the printed theorem through
the bundle therefore needs the contradiction stated with membership only at
the image of the Kazhdan source, which is this file.

* `lambda_cocycle_pointwise` is `CollapseLambdaCocycle.lambda_cocycle_almost`
  at one pair: the cocycle inference never looks at the family away from the
  three elements it relates, so the global `d : H → rankIdeal` binder was
  packaging, not content.
* `collapse_contradiction_localized` is
  `collapse_contradiction_printed` with the displacement family carried as a
  plain corona-valued function together with membership at `iota Γ` only.
  The compressed displacements `d_{sγs⁻¹}` are hypothesised to vanish — the
  printed *"the hypothesis on `p` gives `d_{sγs^{-1}} = 0`"* — and `0` is in
  every submodule, so no membership is owed there either.

The proof is the bundle's proof; what moved is where the subtype is formed.
-/

namespace GroupApproximation
namespace CollapsePrintedContradiction

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection
open RankNormalizedLambda RankNormalizedHilbertization
open CollapseLambdaCocycle
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

section Pointwise

variable {H : Type u} [Group H] (A : OpAlmostRepresentation H)
  [∀ n, Nonempty (A.model n)]

/-- **The cocycle inference at one pair.**  The proof of
`CollapseLambdaCocycle.lambda_cocycle_almost` uses its family `d` and its
global identity `hd` only at the three elements `g * h`, `g`, `h`, so the
inference holds with exactly those values given.  This is what lets the
displacement family be subtyped into the ideal only where membership is
actually proved. -/
theorem lambda_cocycle_pointwise (P : MatFam A.model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (g : H)
    (dg dh dgh : rankIdeal A.model P)
    (hd : (dgh : NormMatrixCStarCorona (fun n ↦ A.model n))
      = (dg : NormMatrixCStarCorona (fun n ↦ A.model n))
        + coronaLinear A.model
            (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
          (dh : NormMatrixCStarCorona (fun n ↦ A.model n)) *
          star (coronaLinear A.model
            (unitarySequenceBounded A.model (fun n ↦ A.map n g)))) :
    lambda A.model P ω hω dgh
      = lambda A.model P ω hω dg
        + OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
            (rankWeight_nonneg A.model P) g (lambda A.model P ω hω dh) := by
  have hmem : coronaLinear A.model
      (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
      (dh : NormMatrixCStarCorona (fun n ↦ A.model n)) *
      star (coronaLinear A.model
        (unitarySequenceBounded A.model (fun n ↦ A.map n g)))
      ∈ rankIdeal A.model P :=
    mul_mem_rankIdeal A.model P _ _ dh.2
  have heq : OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
      (rankWeight_nonneg A.model P) g (lambda A.model P ω hω dh)
      = lambda A.model P ω hω ⟨_, hmem⟩ := by
    show OmegaIsometryRepresentation.repEquiv A (rankWeight A.model P) ω hω
        (rankWeight_nonneg A.model P) g (lambda A.model P ω hω dh) = _
    rw [OmegaConjQCompatibility.repEquiv_eq_conjIsometryEquiv A
      (rankWeight A.model P) ω hω (rankWeight_nonneg A.model P) g]
    exact conjIsometryEquiv_lambda A.model P ω hω (fun n ↦ A.map n g) dh
      ⟨_, hmem⟩ rfl
  have hsum : dgh = dg + ⟨_, hmem⟩ := Subtype.ext hd
  rw [heq, hsum, map_add]

end Pointwise

section Localized

variable {Γ H : Type} [Group Γ] [Group H] (A : OpAlmostRepresentation H)
  [∀ n, Nonempty (A.model n)] (ω : Ultrafilter ℕ)

/-- **The printed contradiction, with the displacement family valued in the
corona and membership only at the Kazhdan image.**

Compared to `CollapseCompressionBundle.collapse_contradiction_printed`, the
family `dcor` is a plain function into the corona: `hmem` supplies `𝓘_q`
membership at `iota γ` only, which is where the printed induction proves it,
and the compressed displacements are hypothesised to vanish outright, which is
what the printed hypothesis on `p` gives.  Nothing about `dcor` away from
`iota Γ` and its `s`-conjugates is consumed. -/
theorem collapse_contradiction_localized (hω : (ω : Filter ℕ) ≤ cofinite)
    (hT : HasKazhdanPropertyT.{0, 0} Γ) (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (P : MatFam A.model)
    (dcor : H → NormMatrixCStarCorona (fun n ↦ A.model n))
    (hd : ∀ g h : H,
      dcor (g * h)
        = dcor g
          + coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
            dcor h *
            star (coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g))))
    (hmem : ∀ γ : Γ, dcor (iota γ) ∈ rankIdeal A.model P)
    (hcompressed : ∀ γ : Γ, dcor (s * iota γ * s⁻¹) = 0)
    (hne : ∃ γ : Γ,
      lambda A.model P ω hω ⟨dcor (iota γ), hmem γ⟩ ≠ 0) : False := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, _hkpos, _hkone, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  refine CollapseDelormeCorona.collapse_contradiction_corona_delorme
    A.model ω (rankWeight A.model P) (rankWeight_nonneg A.model P)
    (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa hpair S
      (Finset.Subset.refl S) hone hsymm hgen hs)
    hT (fun γ ↦ lambda A.model P ω hω ⟨dcor (iota γ), hmem γ⟩) ?_ ?_ hne
  · intro γ δ
    have hjoin := CollapseRouteJoin.coronaRep_omegaCompressionRep A ω hω
      (rankWeight A.model P) (rankWeight_nonneg A.model P) iota s S kappa hpair
      S (Finset.Subset.refl S) hone hsymm hgen hs γ
    have hcoc := lambda_cocycle_pointwise A P ω hω (iota γ)
      ⟨dcor (iota γ), hmem γ⟩ ⟨dcor (iota δ), hmem δ⟩
      ⟨dcor (iota γ * iota δ), by rw [← map_mul]; exact hmem (γ * δ)⟩
      (hd (iota γ) (iota δ))
    have hdval : (⟨dcor (iota (γ * δ)), hmem (γ * δ)⟩ :
        rankIdeal A.model P)
        = ⟨dcor (iota γ * iota δ),
            by rw [← map_mul]; exact hmem (γ * δ)⟩ := by
      apply Subtype.ext
      show dcor (iota (γ * δ)) = dcor (iota γ * iota δ)
      rw [map_mul]
    show lambda A.model P ω hω ⟨dcor (iota (γ * δ)), hmem (γ * δ)⟩
      = lambda A.model P ω hω ⟨dcor (iota γ), hmem γ⟩
        + CollapseDelormeCorona.coronaRep A.model ω (rankWeight A.model P)
            (rankWeight_nonneg A.model P)
            (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa
              hpair S (Finset.Subset.refl S) hone hsymm hgen hs) γ
            (lambda A.model P ω hω ⟨dcor (iota δ), hmem δ⟩)
    rw [hdval, hjoin]
    exact hcoc
  · intro a
    have hi : iota (CollapseTransportEndpoint.compressionMap A.model ω
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa
          hpair S (Finset.Subset.refl S) hone hsymm hgen hs) a)
        = s * iota a * s⁻¹ :=
      CollapseTransportEndpoint.iota_compressionMap A.model ω
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa
          hpair S (Finset.Subset.refl S) hone hsymm hgen hs) a
    show lambda A.model P ω hω
      ⟨dcor (iota (CollapseTransportEndpoint.compressionMap A.model ω
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa
          hpair S (Finset.Subset.refl S) hone hsymm hgen hs) a)),
        hmem _⟩ = 0
    have hz : (⟨dcor (iota (CollapseTransportEndpoint.compressionMap A.model ω
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa
          hpair S (Finset.Subset.refl S) hone hsymm hgen hs) a)),
        hmem _⟩ : rankIdeal A.model P) = 0 := by
      apply Subtype.ext
      show dcor (iota (CollapseTransportEndpoint.compressionMap A.model ω
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa
          hpair S (Finset.Subset.refl S) hone hsymm hgen hs) a))
        = (0 : NormMatrixCStarCorona (fun n ↦ A.model n))
      rw [hi]
      exact hcompressed a
    rw [hz, map_zero]

end Localized

end

end CollapsePrintedContradiction
end GroupApproximation
