import GroupApproximation.Analysis.CollapseRouteJoin

/-!
# The printed contradiction, from the printed hypotheses

Proof-ledger rows `CO.21`, `CO.21b` and `CO.04`.  The pieces of the printed
proof of `thm:projection-collapse` are all in the corpus:

* `CollapseLambdaCocycle.lambda_cocycle_almost` — `β(g) = Λ(d_g)` is a cocycle
  for the representation an operator-norm almost representation induces on
  `K_ω`, which is the printed `π(h) = [Ad U_n(h)]_ω`;
* `CollapseDelormeCorona.collapse_contradiction_corona_delorme` — the printed
  last paragraph, with Delorme–Guichardet proved, `htransport` proved and `π`
  built, assuming only the cocycle;
* `CollapseRouteJoin.coronaRep_omegaCompressionRep` — the two representations
  are the same map once the Kazhdan compression bundle is built from the
  almost representation.

What was left was assembly, and this file does it.  `collapse_contradiction_printed`
takes the hypotheses the *theorem statement* has — an almost representation, a
Kazhdan source with property (T), a compressing element, and a displacement
family in the ideal satisfying `eq:collapse-cocycle` in the corona — and
derives the contradiction, with no bundle, no Kazhdan pair and no
representation supplied by the caller.

## Where the bundle data comes from

`omegaCompressionRep` wants a Kazhdan pair together with a symmetric
generating set containing it.  That is not an extra hypothesis:
`HasKazhdanPropertyT` is *by definition* the existence of a Kazhdan pair, and
`KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair`
already upgrades it to
the symmetric generating form — which is the printed opening sentence
*"property (T) makes `L` finitely generated; fix a finite symmetric generating
set"*.  So the extraction is an `obtain`, and this file adds no assumption
that the printed theorem does not make.

## The compressed hypothesis is the printed one

`hcompressed` below is stated as the print states it, `d_{sγs⁻¹} = 0`, rather
than through the bundle's chosen compression map; `iota_compressionMap`
converts.  That keeps the statement readable against the manuscript instead of
against the bundle's internals.

The bundle and `Sofic/OmegaWeightedAmbient` are not touched: this file
consumes `omegaCompressionRep` exactly as stated.
-/

namespace GroupApproximation
namespace CollapseCompressionBundle

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection
open RankNormalizedLambda RankNormalizedHilbertization

noncomputable section

variable {Γ H : Type} [Group Γ] [Group H] (A : OpAlmostRepresentation H)
  [∀ n, Nonempty (A.model n)] (ω : Ultrafilter ℕ)

/-- **The printed contradiction of `thm:projection-collapse`, from the printed
hypotheses.**

`A` is the almost representation carrying the printed unitary coordinate lifts
of `lem:unitarycorona`; `iota` and `s` are the printed Kazhdan subgroup and
compressor; `d` is the displacement family, valued in the ideal `𝓘_q` by
`CollapseDisplacementIdeal.displacement_mem_rankIdeal`, and `hd` is
`eq:collapse-cocycle` in the corona.  `hcompressed` is the printed
`d_{sγs⁻¹} = 0`, and `hne` is the nonvanishing of `β`, which
`CollapseLambdaCocycle.not_all_lambda_eq_zero` supplies.

Everything else the printed proof uses is derived here: the Kazhdan pair and
its symmetric generating set from property (T), the compression bundle from
the almost representation, the cocycle from `lambda_cocycle_almost`, the
identification of the two representations from `coronaRep_omegaCompressionRep`,
and the contradiction from the Delorme endpoint. -/
theorem collapse_contradiction_printed (hω : (ω : Filter ℕ) ≤ cofinite)
    (hT : HasKazhdanPropertyT.{0, 0} Γ) (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (P : MatFam A.model) (d : H → rankIdeal A.model P)
    (hd : ∀ g h : H,
      (d (g * h) : NormMatrixCStarCorona (fun n ↦ A.model n))
        = (d g : NormMatrixCStarCorona (fun n ↦ A.model n))
          + coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ A.model n)) *
            star (coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g))))
    (hcompressed : ∀ γ : Γ,
      lambda A.model P ω hω (d (s * iota γ * s⁻¹)) = 0)
    (hne : ∃ γ : Γ, lambda A.model P ω hω (d (iota γ)) ≠ 0) : False := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, _hkpos, _hkone, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  refine CollapseDelormeCorona.collapse_contradiction_corona_delorme
    A.model ω (rankWeight A.model P) (rankWeight_nonneg A.model P)
    (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa hpair S
      (Finset.Subset.refl S) hone hsymm hgen hs)
    hT (fun γ ↦ lambda A.model P ω hω (d (iota γ))) ?_ ?_ hne
  · intro γ δ
    have hjoin := CollapseRouteJoin.coronaRep_omegaCompressionRep A ω hω
      (rankWeight A.model P) (rankWeight_nonneg A.model P) iota s S kappa hpair
      S (Finset.Subset.refl S) hone hsymm hgen hs γ
    have hcoc := CollapseLambdaCocycle.lambda_cocycle_almost A P ω hω d hd
      (iota γ) (iota δ)
    show lambda A.model P ω hω (d (iota (γ * δ)))
      = lambda A.model P ω hω (d (iota γ))
        + CollapseDelormeCorona.coronaRep A.model ω (rankWeight A.model P)
            (rankWeight_nonneg A.model P)
            (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa
              hpair S (Finset.Subset.refl S) hone hsymm hgen hs) γ
            (lambda A.model P ω hω (d (iota δ)))
    rw [map_mul iota, hjoin]
    exact hcoc
  · intro a
    have hi : iota (CollapseTransportEndpoint.compressionMap A.model ω
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa hpair
          S (Finset.Subset.refl S) hone hsymm hgen hs) a)
        = s * iota a * s⁻¹ :=
      CollapseTransportEndpoint.iota_compressionMap A.model ω
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa hpair
          S (Finset.Subset.refl S) hone hsymm hgen hs) a
    show lambda A.model P ω hω (d (iota
      (CollapseTransportEndpoint.compressionMap A.model ω
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s S kappa hpair
          S (Finset.Subset.refl S) hone hsymm hgen hs) a))) = 0
    rw [hi]
    exact hcompressed a

end

end CollapseCompressionBundle
end GroupApproximation
