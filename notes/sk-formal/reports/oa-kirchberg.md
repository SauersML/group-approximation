# oa-kirchberg: Kirchberg's Theorem 1.1 for `simple_kazhdan_sofic_group.tex`

Lane oa-kirchberg is a fork of main, launched 2026-09-13 ~20:15. Its brief is the "OA LANES 20:15" row of `ct/ROSTER-sk.md` in main's scratchpad.
The note is at e80dcf20a (md5 4ad4921253626a4f858866c716a13385), census 09e580c38.

## CLAIM

CLAIM Kirchberg Theorem 1.1, closed inhabitant of `KirchbergKazhdanFactorizationInput` GroupApproximation/Manuscript/NinetyNineProblems/KirchbergTheorem.lean
CLAIM real dilation of positive definite matrix functions on a group GroupApproximation/Analysis/KirchbergRealDilation.lean
CLAIM completed real tensor square with the diagonal orthogonal representation and its operator field GroupApproximation/Analysis/KirchbergTensorSquare.lean
CLAIM compact positive operators have finite-dimensional eigenspaces; invariant compact operators live on finite-dimensional subrepresentations GroupApproximation/Analysis/KirchbergCompactExtraction.lean
CLAIM almost invariant vectors are near invariant vectors (Kazhdan pair, real) GroupApproximation/Kazhdan/KazhdanNearInvariantVector.lean
CLAIM finite-dimensional orthogonal representations separating points give residual finiteness GroupApproximation/Algebra/OrthogonalRepresentationResiduallyFinite.lean
CLAIM amenable-trace models give positive definite matrix functions GroupApproximation/Analysis/KirchbergTraceModels.lean
CLAIM printed sentences d4c75e0d3c7f and the first clause of 1fe81fb1330c GroupApproximation/Manuscript/SimpleKazhdanSofic/KirchbergFactorizationSentences.lean

CLAIM completion of a linear isometry representation GroupApproximation/Analysis/KirchbergCompletionRepresentation.lean
CLAIM realified Frobenius and trace identities for complex matrix models GroupApproximation/Analysis/KirchbergRealForms.lean

CLAIM Kirchberg Corollary 1.2, every subgroup of the unitary group of R has the factorization property GroupApproximation/Analysis/KirchbergHyperfiniteSubgroups.lean
CLAIM printed rows 88ecdc10f78b (Theorem 1.1 and Corollary 1.2) and a63ff00e499b (G lacks the factorization property; G is not a subgroup of U(R)) GroupApproximation/Manuscript/SimpleKazhdanSofic/KirchbergFactorizationSentences.lean

00:0x: main widened the scope to Corollary 1.2 and "G is not a subgroup of U(R)". The tensor-form equivalence is not needed.

09-14 08:5x after the reboot (infra rebuilt; all green records lost):
- LANDED 2aea5d2b5 (probe 0914-014232-348, BUILT): `Kazhdan/KazhdanNearInvariantVector`, `Algebra/OrthogonalRepresentationResiduallyFinite`, `Analysis/KirchbergTraceModels`.
- LANDED 0432a7d3a (probe 0914-083157-34192, BUILT): `Analysis/KirchbergCompletionRepresentation`, `Analysis/KirchbergRealForms`.
- All five are wire-queued.
- Fixing and re-probing: `KirchbergCompactExtraction` (lint only), `KirchbergRealDilation` (a missing `open Matrix` cascaded). After those: `KirchbergTensorSquare` and the assembly `Manuscript/NinetyNineProblems/KirchbergTheorem`.
- Corollary 1.2 plan, trace side:
  - pull the amenable models of R's matrix stages back along G → U(R) (`PalomarBridges/X1.isAmenableTrace_comp`);
  - tensor powers and Cesàro averages kill the traces of non-scalar and of scalar elements;
  - finish with the dense-generator upgrade (`amenableTraceModel_of_dense_generators`).
- This consumes oa-hyperfinite's Pauli model `Hyperfinite.hyperfiniteFactor`: its matrix stages and trace-preserving expectations are not on origin yet.

01:30 status:
- All eight infrastructure modules plus the assembly are drafted (attic copies on main), with a co-probe running.
- Endpoints planned in `Manuscript/NinetyNineProblems/KirchbergTheorem`: `kirchbergKazhdanFactorizationInput`, `printedKirchbergTheorem`, `not_hasFactorizationProperty_of_simple_infinite_kazhdan`.

23:35 re-scope: the note is at 37551fd93 (census 649cb1f80, md5 b55c0d23…), section "Brown's formulation" l.283–290.
- Rows: `88ecdc10f78b` (Theorem 1.1, plus a new clause: Corollary 1.2, every subgroup of U(R) has the factorization property) and `a63ff00e499b` (G lacks the factorization property; G is not a subgroup of U(R); the LLP clause belongs to oa-llp).
- G is "a group as in Theorem thm:general": infinite, finitely generated, simple and Kazhdan.

Absorbed oa-cstar-group (not resumed, 23:15). It wrote only its report, never landed and now gone from disk. It had no Lean drafts. Its claims are released:
- `Analysis/GroupCStarRegularTensor`, `Analysis/GroupCStarPositiveDefiniteDilation`, `Analysis/FactorizationTraceToTensor`.
- The planned content was λ·ρ on C*(G) ⊗ C*(G), the tensor form of the factorization property, and both directions of Brown's equivalence.
- No printed step on this route consumes the tensor form: the repo definition is the trace side, which is Ozawa's Def 7.2 (F) via Thm 6.1 (ii). oa-llp consumes the trace side too.
- The complex dilation it planned is replaced here by the real dilation in `KirchbergRealDilation`.

Ownership check, 20:25: no origin declaration inhabits `KirchbergKazhdanFactorizationInput`. No `lanes/*.files` entry and no other swarm's scratchpad names Kirchberg's Theorem 1.1. The `BlackadarKirchberg*` and `KirchbergRordam*` modules are different theorems.

## Printed text (census 09e580c38)

- `d4c75e0d3c7f` (l.173–175): "Kirchberg proved that a Kazhdan group with the factorization property is residually finite [Theorem 1.1]."
- `1fe81fb1330c` (l.175–177): "So G does not have the factorization property, and C*(G) does not have the local lifting property [p. 527]."
  This lane owns the first clause; oa-llp owns the LLP clause.

## Statement on origin

- `HasFactorizationProperty G` is `Quasidiagonal.IsAmenableTrace` of `canonicalMaximalTrace G`. It asks for ucp matrix models of C*_max(G) that are asymptotically multiplicative in the normalized Hilbert–Schmidt norm and whose normalized traces converge to τ. That is the trace side of Brown's equivalence.
- `KirchbergKazhdanFactorizationInput.{u}`: for every countable `G : Type u` with `HasKazhdanPropertyT.{u,u} G` and `HasFactorizationProperty G`, `IsResiduallyFinite G`.

## Route (trace side, no tensor-norm input)

1. Let φₙ be the models and h ≠ 1. Realify φₙ(u_g) to Φₙ(g) ∈ M_{2k}(ℝ).
   - Complete positivity makes Φₙ a positive definite matrix function on G.
   - The model estimates give (1/2k)‖Φₙ(q)‖²_F → 1 at each q, and (1/2k) tr Φₙ(h) → Re τ(u_h) = 0.
2. Dilation: a real Hilbert space K in `Type u`, an orthogonal representation σ of G, and an isometry V : ℝ^{2k} → K with ⟨σ(g)Vv, Vw⟩ = ⟨Φₙ(g)v, w⟩.
3. On the completed real tensor square E = K ⊗̂ K, the diagonal representation σ⊗σ has the unit vector η = (2k)^{-1/2} Σⱼ Vfⱼ ⊗ Vfⱼ.
   - ‖(σ⊗σ)(q)η − η‖² = 2 − 2(1/2k)‖Φₙ(q)‖²_F.
   - ⟨(σ(h)⊗1)η, η⟩ = (1/2k) tr Φₙ(h).
4. Kazhdan pair (Q, ε): there is an invariant ζ with ‖ζ − η‖ ≤ ε⁻¹ max_q ‖(σ⊗σ)(q)η − η‖.
5. ζ defines a compact operator T_ζ on K with ⟨T_ζ y, x⟩ = ⟨ζ, x⊗y⟩, commuting with σ(G).
   - Moreover T_{(A⊗1)ζ} = A T_ζ, and ζ ↦ T_ζ is injective.
6. Extraction. Let M be the closed span of the finite-dimensional σ-invariant subspaces, and S = (1 − P_M)T_ζ.
   - SSᵀ is compact, positive and σ-equivariant. If it is nonzero it has an eigenvalue μ > 0, and its eigenspace is finite-dimensional, invariant and contained in M^⊥, which is impossible. So T_ζ = P_M T_ζ.
   - If σ(h) fixed every finite-dimensional invariant subspace pointwise, then σ(h)T_ζ = T_ζ, so (σ(h)⊗1)ζ = ζ.
   - That forces ⟨(σ(h)⊗1)ζ, ζ⟩ = ‖ζ‖². But for large n the left side is near 0 and ‖ζ‖² is near 1.
7. So some finite-dimensional orthogonal representation moves h. G is finitely generated (`fg_of_hasKazhdanPropertyT`), and Mal'cev (`MalcevLinear.residuallyFinite_of_fg`) turns the image into a finite quotient that separates h.
