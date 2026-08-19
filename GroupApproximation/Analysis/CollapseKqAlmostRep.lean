import GroupApproximation.Analysis.CollapseKqTransport
import GroupApproximation.Analysis.CollapseLambdaCocycle
import GroupApproximation.Analysis.OmegaConjQCompatibility
import GroupApproximation.Analysis.CollapsePrintedContradiction

/-!
# The printed collapse paragraph on `K_q`, at the generality the printed route
supplies

Proof-ledger rows `CO.21` and `CO.21b`.  Both rows record the same remaining
gap, in the same words:

> `CollapseInvariantSubspace.collapse_contradiction_Kq` and its printed form
> take `Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)` — a COORDINATEWISE
> homomorphism.  `printed_projection_collapse` has no such object and cannot
> have one: its `Θ` is a homomorphism into
> `unitary (NormMatrixCStarCorona …)`, and the coordinatewise object the
> printed route obtains from it through `lem:unitarycorona` is
> `coronaAlmostRep`, an `OpAlmostRepresentation`, which is multiplicative only
> asymptotically.

This file removes that gap.  The `K_q` paragraph is restated for an
operator-norm *almost* representation, which is exactly what the printed route
has, and nothing in it is weakened: the objects, the space and the
representation are the printed ones.

## Why an almost representation is enough

`OmegaIsometryRepresentation.rep` is already a homomorphism `H →* (K_ω ≃ₗᵢ K_ω)`
for an `OpAlmostRepresentation`: the coordinate lifts are only asymptotically
multiplicative, and freeness of `ω` makes the classes multiply exactly.  What
was missing was the two facts that connect it to `K_q`, and both are one
rewrite away from statements already in the tree:

* **Invariance.**  `OmegaConjQCompatibility.repEquiv_eq_conjIsometryEquiv` says
  `rep A g` *is* `conjIsometryEquiv` of the coordinate family `n ↦ A.map n g`,
  and `CollapseInvariantSubspace.conjIsometryEquiv_mem_Kq` preserves `K_q` for
  an arbitrary such family.  So `rep A g` preserves `K_q`, and
  `CollapseInvariantSubspace.restrictUnitary` turns it into a representation of
  `H` on `K_q`.
* **The cocycle.**  `CollapseLambdaCocycle.lambda_cocycle_almost` is `CO.21`'s
  identity for `rep A` already; reading it inside `K_q` is `Subtype.ext`.

## What this closes and what it does not

The transport is carried at *ambient* strength, exactly as in
`Analysis/CollapseKqTransport`: `restrictUnitary_transport` inherits it from
`K_ω`, and the ambient statement for `rep A` is what
`CollapseTransportEndpoint.transport_corona` proves once
`CollapseRouteJoin.coronaRep_omegaCompressionRep` identifies `rep A ∘ ι` with
the bundle's representation.  So the printed paragraph on the printed space
costs no hypothesis the ambient route did not already cost, and it no longer
asks for a coordinatewise homomorphism the printed route cannot supply.
-/

namespace GroupApproximation
namespace CollapseKqAlmostRep

open Filter Matrix Topology
open UltraproductModelConstruction RankNormalizedHilbertization
open KOmegaHilbert CollapseCocycleAnalytic CollapseUltraproductRepresentation
open RankNormalizedLambda CollapseLambdaCocycle CollapseInvariantSubspace
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {H : Type u} [Group H] (A : OpAlmostRepresentation H)
  [∀ n, Nonempty (A.model n)]

/-! ## `K_q` is invariant under the printed `π` -/

/-- **`K_q` is invariant under `rep A`.**  `rep A g` is `conjIsometryEquiv` of
the coordinate family `n ↦ A.map n g`, by
`repEquiv_eq_conjIsometryEquiv`, and conjugation by any coordinatewise family
preserves `K_q` because the printed ideal is two-sided in the corona. -/
theorem rep_mem_Kq (P : MatFam A.model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (g : H) (x : KRank A.model P ω)
    (hx : x ∈ Kq A.model P ω hω) :
    OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
        (rankWeight_nonneg A.model P) g x ∈ Kq A.model P ω hω := by
  have hbridge :
      OmegaIsometryRepresentation.repEquiv A (rankWeight A.model P) ω hω
          (rankWeight_nonneg A.model P) g
        = conjIsometryEquiv A.model (rankWeight A.model P) ω
            (rankWeight_nonneg A.model P) (fun n ↦ A.map n g) :=
    OmegaConjQCompatibility.repEquiv_eq_conjIsometryEquiv A
      (rankWeight A.model P) ω hω (rankWeight_nonneg A.model P) g
  show OmegaIsometryRepresentation.repEquiv A (rankWeight A.model P) ω hω
      (rankWeight_nonneg A.model P) g x ∈ Kq A.model P ω hω
  rw [hbridge]
  exact conjIsometryEquiv_mem_Kq A.model P ω hω (fun n ↦ A.map n g) x hx

/-- **`π` on `K_q`, for the printed almost representation.**  The printed
*"`π` is a unitary representation of `H` on the closed invariant subspace
`K_q`"*, with `π` the representation the printed route actually has. -/
def repKq (P : MatFam A.model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    H →* (Kq A.model P ω hω ≃ₗᵢ[ℂ] Kq A.model P ω hω) :=
  restrictUnitary
    (OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
      (rankWeight_nonneg A.model P))
    (Kq A.model P ω hω) (fun g x hx ↦ rep_mem_Kq A P ω hω g x hx)

@[simp] theorem coe_repKq (P : MatFam A.model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (g : H) (y : Kq A.model P ω hω) :
    ((repKq A P ω hω g y : Kq A.model P ω hω) : KRank A.model P ω)
      = OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
          (rankWeight_nonneg A.model P) g (y : KRank A.model P ω) := rfl

/-! ## `CO.21` inside `K_q`, for the printed representation -/

/-- **`CO.21` in the printed space, at the printed generality.**  The cocycle
identity with both sides inside `K_q` and `π` the representation an
operator-norm almost representation induces.  Its content is
`lambda_cocycle_almost`; what is new is that the equation is read in the
subspace, which is where the print reads it. -/
theorem betaKq_cocycle_almost (P : MatFam A.model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (d : H → rankIdeal A.model P)
    (hd : ∀ g h : H,
      (d (g * h) : NormMatrixCStarCorona (fun n ↦ A.model n))
        = (d g : NormMatrixCStarCorona (fun n ↦ A.model n))
          + coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ A.model n)) *
            star (coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g))))
    (g h : H) :
    betaKq A.model P ω hω d (g * h)
      = betaKq A.model P ω hω d g
        + repKq A P ω hω g (betaKq A.model P ω hω d h) :=
  Subtype.ext (lambda_cocycle_almost A P ω hω d hd g h)

/-! ## The printed last paragraph -/

/-- **`CO.21b` on `K_q`, at the printed generality.**  Delorme–Guichardet on
the printed closed invariant subspace, for the representation the printed route
supplies.  `K_q` is a complex Hilbert space (`completeSpace_Kq`), `π` acts on it
by isometries (`repKq`), and `β` takes its values there (`betaKq`). -/
theorem collapse_contradiction_Kq_almost (P : MatFam A.model)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (hT : HasKazhdanPropertyT.{u, u} H) (d : H → rankIdeal A.model P)
    (c : H → H)
    (hd : ∀ g h : H,
      (d (g * h) : NormMatrixCStarCorona (fun n ↦ A.model n))
        = (d g : NormMatrixCStarCorona (fun n ↦ A.model n))
          + coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ A.model n)) *
            star (coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g))))
    (hcompressed : ∀ a : H, lambda A.model P ω hω (d (c a)) = 0)
    (htransport : ∀ y : Kq A.model P ω hω,
      (∀ a : H, repKq A P ω hω (c a) y = y) →
        ∀ g : H, repKq A P ω hω g y = y)
    (hne : ∃ g : H, lambda A.model P ω hω (d g) ≠ 0) : False := by
  obtain ⟨g₀, hg₀⟩ := hne
  refine CollapseDelormeEndpoint.collapse_contradiction_of_hasKazhdanPropertyT
    hT (repKq A P ω hω) (betaKq A.model P ω hω d) c
    (betaKq_cocycle_almost A P ω hω d hd)
    (fun a ↦ (betaKq_eq_zero_iff A.model P ω hω d (c a)).2 (hcompressed a))
    htransport ⟨g₀, ?_⟩
  intro hzero
  exact hg₀ ((betaKq_eq_zero_iff A.model P ω hω d g₀).1 hzero)

/-- **The same with the transport at ambient strength**, which is the strength
`CollapseTransportEndpoint.transport_corona` proves.  The subspace statement is
inherited from the ambient one by `CollapseKqTransport.restrictUnitary_transport`,
so the printed paragraph read inside the printed space costs no hypothesis that
the same paragraph read in the ambient did not already cost. -/
theorem collapse_contradiction_Kq_almost_of_ambient (P : MatFam A.model)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (hT : HasKazhdanPropertyT.{u, u} H) (d : H → rankIdeal A.model P)
    (c : H → H)
    (hd : ∀ g h : H,
      (d (g * h) : NormMatrixCStarCorona (fun n ↦ A.model n))
        = (d g : NormMatrixCStarCorona (fun n ↦ A.model n))
          + coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ A.model n)) *
            star (coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g))))
    (hcompressed : ∀ a : H, lambda A.model P ω hω (d (c a)) = 0)
    (hambient : ∀ x : KRank A.model P ω,
      (∀ a : H, OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
        (rankWeight_nonneg A.model P) (c a) x = x) →
      ∀ g : H, OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
        (rankWeight_nonneg A.model P) g x = x)
    (hne : ∃ g : H, lambda A.model P ω hω (d g) ≠ 0) : False :=
  collapse_contradiction_Kq_almost A P ω hω hT d c hd hcompressed
    (CollapseKqTransport.restrictUnitary_transport
      (OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
        (rankWeight_nonneg A.model P))
      (Kq A.model P ω hω) (fun g x hx ↦ rep_mem_Kq A P ω hω g x hx) c hambient)
    hne

/-! ## The localized endpoint, on `K_q`

`Analysis/CollapsePrintedContradiction.collapse_contradiction_localized` is the
shape `printed_projection_collapse` consumes: the Kazhdan group enters through
`iota : Γ →* H`, the displacement family is a plain function into the corona,
and ideal membership is required only at `iota γ`, which is where the printed
induction proves it.  It runs Delorme--Guichardet on the ambient `K_ω`.

`collapse_contradiction_localized_Kq` is the same statement, hypothesis for
hypothesis, run where the print runs it. -/

section Localized

variable {Γ : Type} [Group Γ] {H₀ : Type} [Group H₀]

/-- **The printed contradiction, localized, on `K_q`.**

Identical in hypotheses to
`CollapsePrintedContradiction.collapse_contradiction_localized`, and different
in exactly one respect: Delorme--Guichardet is applied to `π` on the printed
closed invariant subspace `K_q` rather than on the ambient `K_ω`.

Every ingredient is already proved elsewhere and this is their assembly.  The
cocycle is `lambda_cocycle_pointwise`, which is stated for `rep A` and so needs
no homomorphism on the coordinates; `Subtype.ext` reads it inside `K_q`.  The
compressed displacements vanish by `iota_compressionMap`, which is the printed
`d_{sas⁻¹} = 0`.  The transport is `transport_corona` for the compression
bundle `OmegaKazhdanCompression.omegaCompressionRep` built from `A` itself,
carried onto `rep A ∘ ι` by `CollapseRouteJoin.coronaRep_omegaCompressionRep`
and then into the subspace, where it is inherited rather than reproved. -/
theorem collapse_contradiction_localized_Kq (B : OpAlmostRepresentation H₀)
    [∀ n, Nonempty (B.model n)] (P : MatFam B.model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (iota : Γ →* H₀) (s : H₀)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (dcor : H₀ → NormMatrixCStarCorona (fun n ↦ B.model n))
    (hd : ∀ g h : H₀,
      dcor (g * h)
        = dcor g
          + coronaLinear B.model
              (unitarySequenceBounded B.model (fun n ↦ B.map n g)) *
            dcor h *
            star (coronaLinear B.model
              (unitarySequenceBounded B.model (fun n ↦ B.map n g))))
    (hmem : ∀ γ : Γ, dcor (iota γ) ∈ rankIdeal B.model P)
    (hcompressed : ∀ γ : Γ, dcor (s * iota γ * s⁻¹) = 0)
    (hne : ∃ γ : Γ,
      lambda B.model P ω hω ⟨dcor (iota γ), hmem γ⟩ ≠ 0) : False := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, _hkpos, _hkone, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  set D := OmegaKazhdanCompression.omegaCompressionRep ω B hω iota s S kappa
    hpair S (Finset.Subset.refl S) hone hsymm hgen hs with hD
  -- `β`, valued in the printed subspace
  set beta : Γ → Kq B.model P ω hω := fun γ ↦
    ⟨lambda B.model P ω hω ⟨dcor (iota γ), hmem γ⟩,
      lambda_mem_Kq B.model P ω hω _⟩ with hbeta
  -- the ambient transport, carried onto `rep B ∘ ι`
  have hjoin : ∀ γ : Γ,
      CollapseDelormeCorona.coronaRep B.model ω (rankWeight B.model P)
          (rankWeight_nonneg B.model P) D γ
        = OmegaIsometryRepresentation.rep B (rankWeight B.model P) ω hω
            (rankWeight_nonneg B.model P) (iota γ) := fun γ ↦
    CollapseRouteJoin.coronaRep_omegaCompressionRep B ω hω
      (rankWeight B.model P) (rankWeight_nonneg B.model P) iota s S kappa hpair
      S (Finset.Subset.refl S) hone hsymm hgen hs γ
  have hamb : ∀ x : KRank B.model P ω,
      (∀ a : Γ, OmegaIsometryRepresentation.rep B (rankWeight B.model P) ω hω
          (rankWeight_nonneg B.model P)
          (iota (CollapseTransportEndpoint.compressionMap B.model ω D a)) x = x) →
      ∀ γ : Γ, OmegaIsometryRepresentation.rep B (rankWeight B.model P) ω hω
        (rankWeight_nonneg B.model P) (iota γ) x = x := by
    intro x hx γ
    have hx' : ∀ a : Γ,
        CollapseDelormeCorona.coronaRep B.model ω (rankWeight B.model P)
            (rankWeight_nonneg B.model P) D
            (CollapseTransportEndpoint.compressionMap B.model ω D a) x = x := by
      intro a
      rw [hjoin (CollapseTransportEndpoint.compressionMap B.model ω D a)]
      exact hx a
    have := CollapseTransportEndpoint.transport_corona B.model ω
      (rankWeight B.model P) (rankWeight_nonneg B.model P) D x hx' γ
    rwa [← hjoin γ]
  -- the transport inside `K_q`, inherited
  have htransport : ∀ y : Kq B.model P ω hω,
      (∀ a : Γ, ((repKq B P ω hω).comp iota)
          (CollapseTransportEndpoint.compressionMap B.model ω D a) y = y) →
        ∀ γ : Γ, ((repKq B P ω hω).comp iota) γ y = y := by
    intro y hy γ
    refine Subtype.ext ?_
    show OmegaIsometryRepresentation.rep B (rankWeight B.model P) ω hω
      (rankWeight_nonneg B.model P) (iota γ) (y : KRank B.model P ω) = _
    refine hamb (y : KRank B.model P ω) (fun a ↦ ?_) γ
    have h := congrArg (fun z : Kq B.model P ω hω ↦ (z : KRank B.model P ω))
      (hy a)
    exact h
  obtain ⟨γ₀, hγ₀⟩ := hne
  refine CollapseDelormeEndpoint.collapse_contradiction_of_hasKazhdanPropertyT
    hT ((repKq B P ω hω).comp iota) beta
    (CollapseTransportEndpoint.compressionMap B.model ω D) ?_ ?_ htransport
    ⟨γ₀, ?_⟩
  · -- the cocycle, read inside `K_q`
    intro γ δ
    refine Subtype.ext ?_
    show lambda B.model P ω hω ⟨dcor (iota (γ * δ)), hmem (γ * δ)⟩
      = lambda B.model P ω hω ⟨dcor (iota γ), hmem γ⟩
        + OmegaIsometryRepresentation.rep B (rankWeight B.model P) ω hω
            (rankWeight_nonneg B.model P) (iota γ)
            (lambda B.model P ω hω ⟨dcor (iota δ), hmem δ⟩)
    have hval : (⟨dcor (iota (γ * δ)), hmem (γ * δ)⟩ : rankIdeal B.model P)
        = ⟨dcor (iota γ * iota δ), by rw [← map_mul]; exact hmem (γ * δ)⟩ := by
      refine Subtype.ext ?_
      show dcor (iota (γ * δ)) = dcor (iota γ * iota δ)
      rw [map_mul]
    rw [hval]
    exact CollapsePrintedContradiction.lambda_cocycle_pointwise B P ω hω
      (iota γ) ⟨dcor (iota γ), hmem γ⟩ ⟨dcor (iota δ), hmem δ⟩
      ⟨dcor (iota γ * iota δ), by rw [← map_mul]; exact hmem (γ * δ)⟩
      (hd (iota γ) (iota δ))
  · -- the compressed displacements vanish
    intro a
    refine Subtype.ext ?_
    show lambda B.model P ω hω
      ⟨dcor (iota (CollapseTransportEndpoint.compressionMap B.model ω D a)),
        hmem _⟩ = (0 : KRank B.model P ω)
    have hz : (⟨dcor (iota (CollapseTransportEndpoint.compressionMap B.model ω D
        a)), hmem _⟩ : rankIdeal B.model P) = 0 := by
      refine Subtype.ext ?_
      show dcor (D.iota (CollapseTransportEndpoint.compressionMap B.model ω D a))
        = (0 : NormMatrixCStarCorona (fun n ↦ B.model n))
      rw [CollapseTransportEndpoint.iota_compressionMap B.model ω D a]
      exact hcompressed a
    rw [hz, map_zero]
  · intro hzero
    exact hγ₀ (congrArg (fun z : Kq B.model P ω hω ↦ (z : KRank B.model P ω))
      hzero)

end Localized

end

end CollapseKqAlmostRep
end GroupApproximation
