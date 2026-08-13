# Group Approximation and Rigidity

[![Lean Prover CI](https://github.com/SauersML/group-approximation/actions/workflows/prover.yml/badge.svg?branch=main)](https://github.com/SauersML/group-approximation/actions/workflows/prover.yml?query=branch%3Amain)

A Lean 4 research library for finite models of groups and the rigidity,
operator-algebraic, combinatorial, and ring-theoretic structures that govern
them. The root module is `GroupApproximation.lean`; it imports the formal
library as a whole, while the subject directories provide smaller reading
paths.

## Verified snapshot

`main` advances continuously while research is in progress. The branch
[`verified`](https://github.com/SauersML/group-approximation/tree/verified)
always points at the newest commit that passed the full Lean Prover CI gate:
`lake build` with warnings as errors, the source and compiled-environment
scans, the non-MF counterpart contract, the kernel-level axiom audit,
signature pinning, and the fresh-kernel `leanchecker` replay. CI advances
the branch automatically after every green run on `main`; nothing else moves
it. To review or build the formal development at a checked state:

```text
git clone --branch verified https://github.com/SauersML/group-approximation.git
```

## An explicit finitely presented CDE-MF obstruction

[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every
countable group is MF in the Carrión–Dadarlat–Eckhardt sense. Here MF means
embeddable as a group into the unitary group of an operator-norm matrix
corona

```text
∏ₙ M_{dₙ}(ℂ) / ⊕ₙ M_{dₙ}(ℂ).
```

The problem has two historical ages: its operator-algebraic lineage begins
with the [1997 Blackadar–Kirchberg MF
program](https://doi.org/10.1007/s002080050039), while the precise MF-group
definition used here first appeared in the [October 2012
Carrión–Dadarlat–Eckhardt preprint](https://arxiv.org/abs/1210.4050),
published in 2013. Thus the result resolves a roughly 29-year-old problem
lineage and a nearly 14-year-old problem in its exact named group form.

The paper gives a finite presentation on eight generators. Start with

```text
Γ = ℤ³ ⋊ SL₃(ℤ),      α(v,A) = (2v,A),      a = (e₁,1),
```

adjoin an HNN letter `t` implementing `α`, and adjoin an involution `c`
centralizing `Γ`. The presentation makes

```text
w = [tct⁻¹, a(tct⁻¹)a⁻¹]
```

a central involution. An explicit Clifford-group representation proves
`w ≠ 1`, while the Kazhdan-compression argument proves that every
homomorphism from the resulting group `E` to every norm matrix corona kills
`w`. Thus `E` is not MF, and neither `C*max(E)` nor `C*red(E)` is an MF
C*-algebra.

The analytic mechanism has four ingredients: cut to the negative corner of
the central involution; pass to the conjugation representation of matrix
lifts; use the Kazhdan projection of `Γ` to obtain nested, unitarily
equivalent fixed-space projections; and use stable finiteness of norm matrix
coronas to force those projections to coincide. This pins `tct⁻¹` to the
`Γ`-fixed space and forces the marked commutator to vanish.

The paper also proves:

- a finite-normal obstruction criterion for any marked Kazhdan-compression
  pattern, without assuming that the map from the Kazhdan group is injective;
- an elementary finite-dimensional kill theorem over every field, requiring
  neither property (T), unitarity, nor centrality of the marked word;
- a cyclic-base comparison showing that the analogous Baumslag–Solitar
  presentation can have an MF representation in which the mark survives;
- a unital separable stably finite non-MF C*-algebra, namely `C*red(E)`;
- failure of closure of MF groups under quotients and split extensions;
- the MF radical and largest MF quotient, scaling families `E_m`, continuum
  many finitely generated non-MF groups, and a uniform matrix-size version of
  the kill theorem;
- closedness of the MF locus in every fixed-rank marked-group space, hence
  openness of non-MF-ness and a finite reduced-word-ball certificate for every
  non-MF marked group;
- a residually finite (hence MF) group whose maximal group C*-algebra contains
  a proper isometry and is therefore not directly finite.

The result is specific to operator-norm approximation. It does not prove that
`E` is nonhyperlinear or nonsofic, does not decide whether
`E/⟨w⟩` is MF, and does not address quasidiagonality of nuclear stably
finite C*-algebras.

### Formal counterpart

The Lean development verifies the marked-compression mechanism, a nontrivial
Clifford mark, and a finitely presented group that is not MF in the standard
cofinite norm-matrix-corona sense; this direct `IsOperatorMF` theorem is the
formal headline. It also proves the stronger universal-ultraproduct kill and,
as an auxiliary consequence, rules out the library's `IsWeakMF` predicate.
The unconditional finitely presented witness is built independently from a
noncomputably chosen Shalom cover; it is not the literal eight-generator
group `E` displayed in the paper. The literal presentation, all displayed
relations, and an exact affine--Clifford realization proving its marked word
nontrivial are formalized separately. No analytic MF endpoint for that
literal group is exported.  The checked theorem
`LiteralBasePropertyTBridge.base_hasKazhdanPropertyT_of_rotation` reduces
property `(T)` of Lean's raw twenty-relator base to property `(T)` of its
eight-relator rotation presentation.  That remaining rotation theorem has
not been proved, and no exact rational group-ring SOS certificate is supplied.
Known property `(T)` of `ℤ³ ⋊ SL₃(ℤ)` does not discharge it without
completeness of the rotation presentation, an isomorphism to the classical
matrix group, or a direct proof. No unconditional literal endpoint or
certificate is asserted.

The general finite-normal obstruction is formalized first as universal
ultraproduct invisibility: `NormMFInvisible` quantifies over every matrix
ultraproduct and every ultrafilter, including principal ultrafilters. This is
not definitionally the manuscript's cofinite-corona radical. It is then
formalized in the unitary-sequence presentation of the cofinite-corona
language. The genuine C-star quotient and the polar-correction isomorphism
from this presentation to its unitary group are formalized in
`Analysis/NormMatrixCorona.lean` and
`Analysis/NormMatrixCoronaUnitary.lean`. For countable groups, a proved bridge
identifies the cofinite-corona MF radical with the ultraproduct residual and
characterizes operator-MF by triviality of that residual; its quotient is MF,
is represented faithfully in one corona, and has the expected universal
factorization property. Other paper consequences are not claimed to be
formalized unless they carry an explicit Lean counterpart link.

The internal definition permits any positive dimension sequence. The
Carrión--Dadarlat--Eckhardt convention requiring strictly increasing
dimensions is proved equivalent by a faithful cumulative block-diagonal
corona embedding; see `Sofic/OperatorMFIncreasingDimensions.lean`.

Reading path, front door first:

| Module | Role |
| --- | --- |
| `Sofic/ChosenNonMFTheorem.lean` | Public chosen finitely presented standard operator-MF endpoint, plus auxiliary weak-MF consequences |
| `Sofic/OperatorMF.lean` | Standard cofinite norm-matrix corona and `IsOperatorMF` |
| `Sofic/CDEOperatorMF.lean`, `Sofic/CDEMFRadical.lean` | Literal countable CDE predicate, genuine C-star-corona equivalence, and CDE radical |
| `Sofic/OperatorMFIncreasingDimensions.lean` | Equivalence with the strictly increasing dimension convention |
| `Sofic/MarkedCompressionSequentialKill.lean` | Universal kill theorem and direct `not_isOperatorMF` / `not_isWeakMF` obstructions |
| `Sofic/MarkedCompressionInclusionData.lean` | Exact one-sided compression interface; no injectivity or endomorphism hypothesis |
| `Sofic/NegativeCornerModel.lean`, `Sofic/ApproxInvolutionCorner.lean` | Involution rounding and negative-corner almost representations |
| `Sofic/KazhdanCompressorCorner.lean`, `Sofic/MarkedCompressionVectorChain.lean` | Adjoint Kazhdan projection, capture, and marked-word collapse |
| `Sofic/AdjointMatrix.lean`, `Sofic/ProjectionRankFlip.lean`, `Sofic/SpectralCapture.lean` | Finite-dimensional operator lemmas |
| `Sofic/MarkedCompressionGroup.lean`, `Sofic/CliffordLampGroup.lean`, `Algebra/MappingTelescope.lean` | Countable Clifford witness and nontrivial mark |
| `Sofic/ChosenMarkedPresentation.lean`, `Sofic/ChosenNonMFEndpoint.lean` | Independent, noncomputably chosen finitely presented witness via a Shalom cover |
| `Sofic/NormMFResidualDetector.lean`, `Sofic/NormMFResidualFunctorial.lean` | Operator-norm MF residual and functoriality |
| `Sofic/NormMFUniversalCorona.lean`, `Sofic/NormMFCoronaRadical.lean` | Equivalence with the unitary-sequence corona radical and largest MF quotient |
| `Sofic/FiniteNormalCompressionObstruction.lean`, `Sofic/FiniteNormalCoronaObstruction.lean` | Finite-normal obstruction in ultraproduct and unitary-sequence corona language |
| `Sofic/LiteralNonMFPresentation.lean`, `Sofic/LiteralNonMFLinearWitness.lean` | Literal eight-generator presentation and exact nontrivial mark |
| `Criterion/FiniteDimensionalKill.lean`, `Sofic/LiteralFiniteDimensionalObstruction.lean` | Finite-dimensional obstruction over an arbitrary field, instantiated for the literal group |
| `Sofic/TorsionFreeFullMFRadical.lean`, `Sofic/TorsionFreeFullMFConsequences.lean` | Proof-carrying Fournier--Facio/Hull defect-routing interface and full CDE-radical consequences; external existence remains explicit |
| `Analysis/TorsionFreeFullMFCStarConsequences.lean` | Reduced-group-C-star non-MF and stable-finiteness consequences of routed data |
| `Sofic/NormMFPrintedConsequences.lean`, `Sofic/NormMFResidualExactQuotient.lean` | Uniform invisibility, portability, and exact quotient factorization |
| `Sofic/OperatorMFPositiveControls.lean`, `Sofic/OperatorMFQuotientNonclosure.lean` | Positive permanence results and explicit quotient nonclosure |
| `Analysis/FaithfulTracialMatrix.lean`, `Analysis/ProperIsometryFromCompression.lean` | Matrix-amplified faithful traces and the proper-isometry obstruction to stable finiteness |
| `Sofic/OperatorMFLocalNormalization.lean`, `Sofic/MarkedMFClosed.lean`, `Sofic/MarkedGroupWordBall.lean` | Local separation normalization, closedness of the marked MF locus, and finite word-ball certificates |
| `Computability/MarkovMFConsequences.lean` | Generic conditional recognition reductions; requires an explicit computable Adian--Rabin transformation and correctness proof |

The headline declarations are included in the kernel audit roster. Their
accepted axiom closure is `propext`, `Classical.choice`, and `Quot.sound`; no
literature theorem is introduced as a Lean axiom.

For the discovery history, first claims, full paper and Lean dependency
graphs, and the role of computation, see
[`docs/NON_MF_ARCHAEOLOGY.md`](docs/NON_MF_ARCHAEOLOGY.md).

## Property (TT)/T and the binary Leavitt algebra

[`property_tt_leavitt.tex`](property_tt_leavitt.tex) develops a second part
of the library: fixed-coordinate matrix factorization and property (TT)/T
over finite-type noncommutative rings. Its principal application is property
(TT)/T for the unit group of the binary Leavitt algebra.

Every numbered result in that paper links visibly to a public Lean
declaration. Its main formal surfaces are:

| Module | Role |
| --- | --- |
| `PropertyTT/PaperStatements.lean` | Statement-level interface for the paper |
| `PropertyTT/LocalizedComplexPlane.lean` | Homogeneous finite-control plane estimate |
| `PropertyT/FreeRootCharacterValuation.lean` | Finite Fourier transport and boundary limits |
| `PropertyTT/FiniteTypeLeavittTT.lean` | Rank-four assembly and all-ranks transport |
| `KOne/PaperStatements.lean` | Rank-two elementary diagonal endpoint |
| `KOne/AllRanksElementaryCore.lean` | All-ranks `GL = E` over the binary Leavitt algebra |

The paper uses the published K-theoretic proof of `K₁ = 0` and `GLₙ = Eₙ`
for the binary Leavitt algebra. Lean reaches the same endpoint independently
through the constructive prefix-code pencil reduction in `KOne/`; external
results are not imported as axioms.

## Library scope

The repository contains several interacting developments:

- sofic, LEF, hyperlinear, and operator-norm matrix approximation;
- Kazhdan property (T), explicit Kazhdan systems, and fixed-point methods;
- expander decomposition and repair arguments;
- matching, finite groupoids, and local-to-global approximation criteria;
- elementary and Steinberg groups over noncommutative rings;
- Leavitt algebras, matrix self-similarity, unstable elementary reduction,
  and Whitehead `K₁`;
- quasi-cocycles and property (TT)/T;
- domination, representation-theoretic obstructions, and finitely presented
  covers.

## Subject map

| Directory | Contents |
| --- | --- |
| Algebra/ | Algebraic infrastructure used across the project |
| Sofic/ | Sofic, LEF, hyperlinear, and matrix approximation |
| Kazhdan/ | Property (T), Hilbert-space geometry, GNS, and fixed points |
| PropertyT/ | Explicit relative estimates and Kazhdan systems for elementary groups |
| PropertyTT/ | Quasi-cocycles, relative (TT), (TT)/T, and globalization |
| Kun/ | Expander decomposition, rounding, repair, and spectral analysis |
| KunThom/ | Centralizer and exact-product expansion arguments |
| Matching/ | Finite groupoids, partial bijections, matching, and completion |
| Criterion/ | Compression and local-to-global non-approximation criteria |
| Leavitt/ | Leavitt families, prefix codes, corners, and rank self-similarity |
| KOne/ | Unstable elementary reduction and K_1 calculations |
| Steinberg/ | Steinberg groups, root systems, and central extensions |
| Covers/ | Finitely presented and Kazhdan covers |
| Domination/ | Finite-dimensional and permutation domination obstructions |
| Monsters/ | Further constructions built from the common infrastructure |
| Endpoint/ | Public theorem surfaces and audit reports |

The docs/ directory is a working research archive as well as documentation.
Files prefixed FALSE_ record investigated approaches that were ruled out;
they are retained so failed routes and their precise obstructions remain
searchable.

## Tool and computational resource disclosure

SauersML is the repository maintainer and responsible author.  The
mathematics and formalization were developed with extensive use of large
language models, including Anthropic Claude and OpenAI Codex models in
multiple concurrent interactive sessions.  Those systems are research and
software tools, not the authors named in `CITATION.cff`; commit trailers and
session records document tool provenance rather than authorship.  The
responsible author reviewed the theorem statements, proofs, formal endpoints,
and literature claims and accepts responsibility for their accuracy.

Formal verification uses Lean 4 and Mathlib, with the Lean kernel as the
final checker.  Model roles, source checks, and successive credit audits are
recorded in [docs/CREDIT_AND_PRIORITY_AUDIT.md](docs/CREDIT_AND_PRIORITY_AUDIT.md).

## Trust and verification

The project pins Lean and Mathlib in `lean-toolchain` and `lake-manifest.json`.
GitHub Actions performs the computational checks:

- Lean Prover CI builds with warnings as errors, runs source and compiled
  environment scans, checks transitive axiom closures, pins mapped theorem
  signatures, and replays compiled objects through a fresh Lean kernel.
- The non-MF and property-(TT)/T PDF workflows validate visible TeX-to-Lean
  references, compile and lint each manuscript, reject unresolved references
  and layout overflow, render every page, validate the PDFs, and commit them
  to `main`.
- Independent kernel re-check is an additional manually triggered audit.
- API documentation publishes the generated Lean documentation.

The accepted axiom closure is restricted to `propext`, `Classical.choice`,
and `Quot.sound`. The audit rejects `sorry`, project axioms, compiler-trust
shortcuts, and theorem-shaped literature assumptions.

Key audit files:

- `scripts/check.py`: source-level checks;
- `scripts/Audit.lean`: statement pins, axiom closure, and environment scans;
- `GroupApproximation/Endpoint/ChosenNonMFAudit.lean`: focused audit of
  the noncomputably chosen non-MF endpoints;
- `scripts/Signatures.lean` and `docs/CLAIM_SIGNATURES.md`: elaborated public
  signatures;
- `scripts/check_non_mf_refs.py` and `scripts/check_property_tt_refs.py`:
  visible manuscript-to-Lean reference checks;
- `docs/PROPERTY_TT_CLAIM_MAP.md`: statement mapping for the property-(TT)/T
  paper.

Cold local builds are expensive. The maintained verification path is the
GitHub Actions workflows in `.github/workflows/`.
