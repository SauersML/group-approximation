# oa-hyperfinite: R, M^ω and the matrix-ultraproduct embedding behind "Brown's formulation" of simple_kazhdan_sofic_group.tex

Lane oa-hyperfinite, launched ~20:15 by main. Brief: `ct/ROSTER-sk.md`, "OA LANES 20:15". No literature input.
Tip: 37551fd93 (767 lines, md5 b55c0d23b8c59e66d36df004a1df608b; census 649cb1f80). "Brown's formulation" is tex l.273–290,
for G as in thm:general.

## Scope (main, 23:15 and 08:4x)
oa-ultrapower is not resumed, so this lane owns the general tracial ultrapower M^ω as well as R. oa-ultrapower left no drafts
and no report. oa-mcduff owns L(G) ↪ R^ω for hyperlinear G, ⊗̄, McDuff, and L(G)⊗̄R ↪ R^ω, and consumes these modules.
After the 09-14 reboot every probe was re-run; records below are from the rebuilt infra.

## CLAIM
CLAIM twisted group von Neumann algebra L_σ(Γ) on ℓ²(Γ) GroupApproximation/Analysis/TwistedGroupVonNeumann.lean
CLAIM twisted-ICC criterion: commutant = scalars, factor, II₁ factor GroupApproximation/Analysis/TwistedGroupVonNeumannFactor.lean
CLAIM the Pauli model R and the interleaving Γ × Γ ≃* Γ GroupApproximation/Analysis/PauliHyperfiniteFactor.lean
CLAIM Pauli operators: unit, adjoint, trace, product rule GroupApproximation/Analysis/PauliStageOperators.lean
CLAIM star homomorphisms from systems of matrix units GroupApproximation/Analysis/MatrixUnitHom.lean
CLAIM Pauli stage matrix units and the unital trace-preserving M_{2^j}(ℂ) → R GroupApproximation/Analysis/PauliMatrixUnits.lean
CLAIM corner embeddings A ↦ A ⊗ 1_r GroupApproximation/Analysis/DyadicCornerEmbedding.lean
CLAIM the tracial ultrapower M^ω of a von Neumann algebra with a tracial vector GroupApproximation/Analysis/TracialUltrapower.lean
CLAIM the ultratrace on M^ω and the diagonal embedding M → M^ω GroupApproximation/Analysis/TracialUltrapowerTrace.lean
CLAIM the stage-corner maps M_k → R (trace factor kr/2^j, norm contractive) GroupApproximation/Analysis/HyperfiniteStageCorner.lean
CLAIM θ: unital trace-preserving ⋆-homomorphism from the tracial matrix ultraproduct into R^ω GroupApproximation/Analysis/MatrixUltraproductToHyperfiniteUltrapower.lean
- WITHDRAWN: `Analysis/HyperfiniteTracialUltrapower.lean`, replaced by the general `Analysis/TracialUltrapower.lean` at M = R.
- Not claimed: the Murray–von Neumann uniqueness of the hyperfinite II₁ factor. The printed R is "the" hyperfinite II₁ factor;
  this lane proves the Pauli model is a hyperfinite II₁ factor.

## State
| module | state |
|---|---|
| TwistedGroupVonNeumann | GREEN a67bd26b3 (0913-204349-15508), wire-queued |
| TwistedGroupVonNeumannFactor | GREEN, landed e793f4f72 (0914-084210-79932), wire-queued |
| TracialUltrapower | GREEN, landed e793f4f72 (0914-084210-79932), wire-queued |
| PauliHyperfiniteFactor | GREEN, bytes 524da3a8f (0914-084844-80248), wire-queued |
| PauliStageOperators | GREEN, bytes 7516942f7 (0914-084844-80248), wire-queued |
| TracialUltrapowerTrace | GREEN, bytes 524da3a8f (0914-084844-80248), wire-queued |
| MatrixUnitHom | GREEN, bytes 050d866ab (0914-090830-4369), wire-queued |
| PauliMatrixUnits | GREEN, bytes ee5d1f867 (0914-091311-84018), wire-queued |
| DyadicCornerEmbedding | GREEN, bytes ee5d1f867 (0914-091311-84018), wire-queued |
| HyperfiniteStageCorner | draft, probing |
| θ (MatrixUltraproductToHyperfiniteUltrapower) | next |

## Route
- R := L_σ(Γ), Γ = Multiplicative (V × V), V = ℕ →₀ ZMod 2, σ((x,z),(x',z')) = Σᵢ zᵢ x'ᵢ. Twisted operators
  (λ_g f)(h) = s(σ(g, g⁻¹h)) f(g⁻¹h) and (ρ_g f)(h) = s(σ(hg⁻¹, g)) f(hg⁻¹), s(z) = (−1)^z; trace T ↦ (Tδ₁)(1).
- Factor criterion `IsTwistedICC σ`: for a ≠ 1, the class of a is infinite, or some t with ta = at has σ(t,a) ≠ σ(a,t).
  The commutant coefficient ξ = Tδ₁ satisfies s(σ(t,t⁻¹a)) s(σ(t⁻¹at,t⁻¹)) ξ(t⁻¹at) = s(σ(t,t⁻¹)) ξ(a). An infinite class
  kills ξ(a) by square-summability; a commuting t with differing values forces ξ(a) = −ξ(a) by the cocycle identities at
  (t,a,t⁻¹) and (a,t,t⁻¹).
- Stages: E_ab = 2^{-j} Σ_z s(z·b) λ_{(a+b, z)} on words of length j; the relations follow from character orthogonality
  Σ_z s(z·c) = 2^j[c = 0]; `stageHom j` is unital with τ(stageHom j A) = 2^{-j} trace A.
- M^ω for a tracial vector Ω: bounded M-valued sequences modulo lim_ω ‖aₙΩ‖ = 0. The ideal is two-sided by traciality,
  ‖TbΩ‖ = ‖b⋆T⋆Ω‖ ≤ ‖b‖‖TΩ‖, with no square roots in M. Ultratrace lim_ω ⟪Ω, aₙΩ⟫; the diagonal embedding preserves it.
- θ: for k = |X n| choose j with k/2^j ≤ 1/(n+1) and r = ⌊2^j/k⌋. A ↦ stageHom j (A ⊗ 1_r) is a contractive ⋆-hom with
  trace factor kr/2^j → 1 and unit defect of trace 1 − kr/2^j < k/2^j. It sends ‖·‖₂-null sequences to null sequences, so
  it descends to a unital, trace-preserving ⋆-hom.

## Ownership check (20:3x, re-checked 23:3x and 08:3x)
- origin, the shared tree, `lanes/*.files` and landed.log have no hyperfinite, ultrapower or twisted group algebra module
  other than this lane's.
- Consumed carriers: `Analysis/GroupVonNeumannAlgebra`, `GroupVonNeumannTrace`, `TwoSidedRegularCommutant`,
  `ReducedGroupCStarTrace(Faithful)`, `TracialStandardFormCommutation`, oa-mcduff's `GroupVonNeumannIIOneFactor`,
  `TracialMatrixUltraproduct`, `TracialQuotientCStar`, `TracialUltraproductCStar`, `Sofic/UltrafilterLimit`.

## Ledger
No census rows of this lane's own: the printed sentences of "Brown's formulation" belong to oa-mcduff, which consumes these modules.
