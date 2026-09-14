# oa-hyperfinite: R, R^ω and embeddings behind "Brown's formulation" of simple_kazhdan_sofic_group.tex

Lane oa-hyperfinite, launched ~20:15 by main. Brief: `ct/ROSTER-sk.md`, "OA LANES 20:15". No literature input.
Tip: 37551fd93 (767 lines, md5 b55c0d23b8c59e66d36df004a1df608b; census 649cb1f80). "Brown's formulation" is tex l.273–290,
for G as in thm:general.

## Scope (main, 23:15)
oa-ultrapower is not resumed. This lane takes back the general tracial ultrapower M^ω and keeps R. oa-ultrapower left no drafts
and no report. oa-mcduff now owns L(G) ↪ R^ω for hyperlinear G, ⊗̄, McDuff, and L(G)⊗̄R ↪ R^ω, and consumes this lane's modules.

## CLAIM
CLAIM twisted group von Neumann algebra L_σ(Γ) on ℓ²(Γ) (twisted regular operators, commutation, trace, separating vector) GroupApproximation/Analysis/TwistedGroupVonNeumann.lean
CLAIM twisted-ICC criterion: the commutant of the twisted two-sided regular representation is the scalars; factor; II₁ factor GroupApproximation/Analysis/TwistedGroupVonNeumannFactor.lean
CLAIM the Pauli model R = L_σ(Multiplicative (V × V)), V = ℕ →₀ ZMod 2, σ(g,k) = z_g · x_k: II₁ factor, and the interleaving Γ × Γ ≃* Γ preserving σ GroupApproximation/Analysis/PauliHyperfiniteFactor.lean
CLAIM the finite Pauli stages: unital trace-preserving M_{2^j} ↪ R from Pauli matrix units, and hyperfiniteness (the stages are 2-norm dense) GroupApproximation/Analysis/PauliMatrixUnits.lean
CLAIM the tracial ultrapower M^ω of a von Neumann algebra with a tracial vector state (bounded sequences in M modulo the 2-norm null ideal along ω, ultratrace), and M ↪ M^ω GroupApproximation/Analysis/TracialUltrapower.lean
CLAIM unital trace-preserving ⋆-homomorphism θ from the tracial matrix ultraproduct into R^ω (dyadic corners M_k ⊗ 1_r ⊂ M_{2^j}) GroupApproximation/Analysis/MatrixUltraproductToHyperfiniteUltrapower.lean
- WITHDRAWN: `Analysis/HyperfiniteTracialUltrapower.lean`, replaced by the general `Analysis/TracialUltrapower.lean` at M = R.

## Model and route
- R := L_σ(Γ) for Γ = Multiplicative (V × V), V = ℕ →₀ ZMod 2, and σ((x,z),(x',z')) = Σᵢ zᵢ x'ᵢ. Twisted operators:
  (λ_g f)(h) = s(σ(g, g⁻¹h)) f(g⁻¹h) and (ρ_g f)(h) = s(σ(hg⁻¹, g)) f(hg⁻¹), with s(z) = (−1)^z.
- Landed at a67bd26b3 (probe 0913-204349-15508 GREEN, BUILT, audits clean): λ_g λ_k = s(σ(g,k)) λ_{gk}; λ and ρ commute; the
  trace T ↦ (Tδ₁)(1) is tracial and faithful on L_σ(Γ); δ₁ separates; L_σ(Γ) is finite.
- Factor criterion, `IsTwistedICC σ`: for every a ≠ 1, the class of a is infinite, or some t with ta = at has σ(t,a) ≠ σ(a,t).
  - T in the commutant satisfies s(σ(t,t⁻¹a)) s(σ(t⁻¹at,t⁻¹)) ξ(t⁻¹at) = s(σ(t,t⁻¹)) ξ(a) for ξ = Tδ₁.
  - An infinite class forces ξ(a) = 0 by square-summability.
  - A commuting t with σ(t,a) ≠ σ(a,t) forces ξ(a) = −ξ(a), by the cocycle identities at (t,a,t⁻¹) and (a,t,t⁻¹).
  - So ξ = ξ(1)δ₁, and T = ξ(1)·1 through the right translates of δ₁.
- Pauli group: every class is a singleton. For a = (x,z) ≠ 0 with xᵢ = 1 take t = (0, eᵢ); with zᵢ = 1 take t = (eᵢ, 0).
- Stages: the span of λ_g with g supported on sites < j is ≅ M_{2^j}. The matrix units are E_bb = 2^{-j} Σ_z s(z·b) Z^z and
  E_ab = X^{a+b} E_bb, and τ(E_ab) = 2^{-j} δ_ab.
- Hyperfinite: for T ∈ R, truncating ξ = Tδ₁ to a finite set F gives S = Σ_{g∈F} ξ(g) λ_g with ‖T − S‖₂ = ‖ξ − ξ_F‖ → 0.
- M^ω: the trace is the vector state ⟪Ω, ·Ω⟫. The null ideal {a : lim_ω ‖aₙΩ‖ = 0} is two-sided by traciality:
  ‖TbΩ‖ = ‖b⋆T⋆Ω‖ ≤ ‖b‖ ‖TΩ‖. So no square roots in M are needed. This covers R, L(G) and L_σ(G × Γ).
- θ: for k = |X n| pick j with k/2^j → 0 and r = ⌊2^j/k⌋. Then A ↦ ι_j(A ⊗ 1_r) is a ⋆-hom with unit defect of trace
  < k/2^j and trace factor kr/2^j → 1. It is 2-norm contractive, so it descends to the quotients as a unital,
  trace-preserving ⋆-hom.
- Notation point: the printed R is "the" hyperfinite II₁ factor. This lane proves the Pauli model is a hyperfinite II₁ factor;
  uniqueness up to isomorphism (Murray–von Neumann) is not claimed.

## Ownership check (20:3x, re-checked 23:3x)
- origin, the shared tree, `lanes/*.files` and landed.log have no hyperfinite, ultrapower or twisted group algebra module
  other than this lane's.
- Consumed carriers: `Analysis/GroupVonNeumannAlgebra`, `GroupVonNeumannTrace`, `TwoSidedRegularCommutant`,
  `ReducedGroupCStarTrace(Faithful)`, `TracialStandardFormCommutation` (`IsFactor`), oa-mcduff's
  `GroupVonNeumannIIOneFactor` (`IsIIOneFactor`, `groupTrace`), `TracialMatrixUltraproduct`, `TracialQuotientCStar`,
  `Sofic/UltrafilterLimit`.

## Landings
- 8f3065896, f3e81c133: claim and scope split.
- a67bd26b3: `TwistedGroupVonNeumann`, GREEN (0913-204349-15508), wire-queued.
- 469c5cc8a: `TwistedGroupVonNeumannFactor`, unverified draft, probing.

## Ledger
No census rows of this lane's own: the printed sentences of "Brown's formulation" belong to oa-mcduff, which consumes these modules.
