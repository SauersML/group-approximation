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

## CLAIM 2 (main, 09-14 09:2x)

CLAIM closed forms of the four Kirchberg-binder consumers of `FactorizationProperty.lean` (l.204, 245, 283, 303) GroupApproximation/Manuscript/NinetyNineProblems/FactorizationPropertyClosed.lean
CLAIM tip l.95 row 660dd9b4b09f, "Thom … not residually finite and so lacks the factorization property", with the inference carried GroupApproximation/Manuscript/SimpleKazhdanSofic/ThomFactorizationSentence.lean

Grading plan for 660dd9b4b09f:
- The sentence cites Thom for the existence of his group (a finitely generated Kazhdan LEF group that is not residually finite) and for "his example is not simple". Nothing later in the note uses that group, so both are credit: `attribution`, as skf-cite graded the Thom sentence at e80dcf20a.
- The sentence asserts the inference "not residually finite and Kazhdan, so it lacks the factorization property". That is carried by a closed endpoint over every group.
- Thom's construction itself stays the typed input `ThomSoficKazhdanNonResiduallyFiniteInput`; it is not proved here.

## Fix (09-14 ~10:20, oa-expanders' fidelity audit)

CLAIM closed `printedGXAnswersBrownOzawaPestov`, the G_X answer to Brown–Ozawa–Pestov GroupApproximation/Manuscript/SimpleKazhdanSofic/GXAnswersBrownOzawaPestovClosed.lean

- **Defect:** row 6866200f2d46 named only the conditional `printedGXAnswersBrownOzawaPestov_of_main` for "G_X answers the question". The closed `printedBrownOzawaPestovAnswer` is about the Pestov91 group, which is a different route.
- **Fix:** close the G_X form from the closed `printedSimpleKazhdanSoficMain`, then re-cite the row.
- LANDED 17af31bea (probe 0914-105742-68430, BUILT, 0 errors), wire-queued. Row 6866200f2d46 now cites the closed `printedGXAnswersBrownOzawaPestov`.
- Main's re-check after sk-lef-assembly's `LEFCharacterizationClosed` landed (83164235d), wrapping sk-lef-action's `printedLamplighterHost`:
  - f8766b1da9e1 flipped partial → formalized, via `printedRecursivelyPresentedLEFHost`.
  - 199438e96aee stays partial. Its first statement is closed (`printedLEFSubgroupCharacterization`); the solvable word problem form waits on `LEFSolvableWordProblemEmbeddingStatement` and `Lamplighter.PrintedLamplighterHostSolvableWordProblem`.
- ms-intro-3's rows 93bcebbc8293 and ca70bdd27b0c (graded partial) still cite the conditional `_of_main`. They could cite the closed form now; that is ms-intro-3's call.

## Item 3 (main, 09-14 ~09:40): SK census rows l.30–88 at census 9cb80166d (tip 8b36733d7, md5 29d63f79)

Checked before writing: no other lane has these keys. 0efbce019168 belongs to sk-stepanov, and 7f3b239e5f2a plus l.89–107 belong to oa-llp.

| key | tex | grade | carriers / residual |
|---|---|---|---|
| 1453f65cbfa2 | abstract l.30–33 | formalized | `printedSimpleKazhdanSoficMain` at n = 3 |
| 6866200f2d46 | abstract l.33–36 | formalized | main's LEF, sofic and hyperlinear clauses; `printedBrownOzawaPestovAnswer`; `printedGXAnswersBrownOzawaPestov_of_main` |
| 199438e96aee | abstract l.37–41 (cor:lef) | partial | converse directions carried; forward directions open on `LamplighterHostStatement`, and for the word-problem form also on `LEFSolvableWordProblemEmbeddingStatement` and `Lamplighter.PrintedLamplighterHostSolvableWordProblem` |
| f8766b1da9e1 | abstract l.42–43 (cor:host) | partial | `printedRecursivelyPresentedLEFHost_of_lamplighter`; open on `LamplighterHostStatement` |
| 43c53c1a6033 | l.73–75 | definition | `IsTextbookLEF` (verbatim), `IsLEF`, `isLEF_iff_textbook` |
| b32e72d0cc49 | l.75–77 | formalized | `printedSubshiftRingFGStatement`, `printedEJZTheorem`, main's (T) clause |
| 48be259e6698 | l.77–80 | formalized | `printedPeriodicMatricialStatement`, `printedFiniteModelsRing` |
| f5bd94aeffeb | l.80–82 | formalized | main's marked-limit clause, `printedMatricialMarkedLimitStatement`, `printedMatricialQuotientsExpanders` |
| 9c6c8ee991ac | l.82–85 | formalized | `printedGeneralSimplicityStatement` via `General.isSimpleGroup_clopenGroupCrossedProduct` (commutator in the H_V ≅ GL_d(F₂) tower copy, then K ⊇ H_V) |
| eadacb5ce412 | l.85–88 | attribution | Matui, credit only |

## CLOSED (09-14 09:2x): claim 2

- LANDED 18e9583b4 (probe 0914-091945-38960, BUILT, 0 errors), wire-queued:
  - `Manuscript/NinetyNineProblems/FactorizationPropertyClosed`:
    - `not_hasFactorizationProperty_of_simple_infinite_kazhdan_closed`;
    - `rankTwelveLeavitt_not_hasFactorizationProperty_closed` (closed, `#audit_closed_axioms`);
    - `not_forall_sofic_hasFactorizationProperty_of_thom` and `not_forall_hyperlinear_hasFactorizationProperty_of_thom`, over Thom's input only.
  - `Manuscript/SimpleKazhdanSofic/ThomFactorizationSentence`: `printedKazhdanNotResiduallyFiniteLacksFactorizationProperty` (closed, audited).
- Row 660dd9b4b09f is landed as `attribution` with the carrier: Thom's construction is credit, and the asserted inference is carried.
- All three rows are keyed by hash at census 649cb1f80/aa6f988f4; re-key when skf-census regenerates at f34e9c0b1.
- Found, not built: `KazhdanQuasidiagonalTraces.KirchbergKazhdanQuasidiagonalInput` (Kazhdan + amenable canonical trace ⇒ quasidiagonal canonical trace) would close from Theorem 1.1 plus "residually finite ⇒ the canonical trace is a limit of finite permutation-representation traces", which is exactly multiplicative models.

## CLOSED (09-14 09:1x): Kirchberg's Theorem 1.1

- LANDED 9df1daac4 (probe 0914-090640, BUILT; `#audit_closed_axioms` passes):
  - `Manuscript/NinetyNineProblems/KirchbergTheorem`: `kirchbergKazhdanFactorizationInput : KirchbergKazhdanFactorizationInput.{u}`, `printedKirchbergTheorem` (no countability) and `not_hasFactorizationProperty_of_simple_infinite_kazhdan`.
  - `Manuscript/SimpleKazhdanSofic/KirchbergFactorizationSentences`: `printedKirchbergTheoremOneOne`, `printedGLacksFactorizationProperty`.
- Infrastructure, all landed and wire-queued: 2aea5d2b5, 0432a7d3a, f00b45b30, and the real dilation plus tensor square.
- Census rows 88ecdc10f78b and a63ff00e499b landed at census 649cb1f80/aa6f988f4 (text verified at 696c4b602).

The note at f34e9c0b1 (09:05) deleted the Kirchberg sentences of "Brown's formulation": Theorem 1.1, Corollary 1.2, "G lacks the factorization property", "G is not a subgroup of U(R)", and the LLP clause. So:
- Both rows will be superseded at the next census regeneration.
- Corollary 1.2 and "not a subgroup of U(R)" are no longer printed. The design below is kept only as a note and is not being built.
- The printed sentence at tip l.95, "Thom constructed … not residually finite and so lacks the factorization property", uses Theorem 1.1's contrapositive, which `printedKirchbergTheorem` carries.

## Corollary 1.2 design (09-14 ~09:00; no longer printed at f34e9c0b1)

Printed claim: every subgroup of U(R) has the factorization property. At the trace side this means: for an injective π : G → U(R), the canonical trace δ₁ of C*(G) is amenable.

Printed route, all steps elementary:
1. **Compression models of τ_R∘π.**
   - Let V_n = M_{2^n}·1̂ ⊂ L²(R) be the Pauli stages, with projection P_n, and φ_n(a) = P_n ρ(a) P_n.
   - These are ucp and contractive on C*_max(G), because ρ is the *-hom extending π.
   - For u ∈ U(R): ‖(1−P_n) u P_n‖₂² / d_n² = ‖u − E_n u‖₂² → 0, and tr(P_n u P_n) / d_n² = τ(u).
   - So τ_R∘π is amenable.
   - Needs from oa-hyperfinite: the stages and their 2-norm density.
2. **Powers.** The k-fold tensor representation π^{⊗k} on L²(R)^{⊗k}, compressed to V_n^{⊗k}, gives models of g ↦ τ(π g)^k.
3. **Averages.** Amplify blocks to a common size and take direct sums: models of τ_N(g) = (1/N) Σ_{k≤N} τ(π g)^k.
4. **Limit.**
   - For g ≠ 1, π(g) ≠ 1.
   - If π(g) is not a scalar, |τ(π g)| < 1 by faithfulness and Cauchy–Schwarz.
   - If π(g) = λ ≠ 1 is a scalar, Cesàro gives (1/N) Σ λ^k → 0.
   - So τ_N → δ₁ on generators. A diagonal choice of models plus `amenableTraceModel_of_dense_generators` finishes.

Shortcut for the clause "G is not a subgroup of U(R)":
- Faithfulness gives Re τ_R(π h) < 1 for π(h) ≠ 1.
- The Theorem 1.1 argument then works with Re tr X(h)/k ≈ Re τ_R(π h) < 1 instead of ≈ 0: take δ below (1 − Re τ_R(π h))/2.
- So a Kazhdan subgroup of U(R) is residually finite, which is the needed contradiction for the note's G. It needs only step 1.

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
