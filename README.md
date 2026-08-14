# Group Approximation and Rigidity

> **Verified state:** the remote `verified` branch is automatically
> fast-forwarded after every complete Lean Prover CI success on `main`.
>
> That branch is the exact repository state most recently certified by
> the full Lean Prover CI gate -- `lake build` with warnings as errors, the
> source and compiled-environment scans, the non-MF counterpart contract,
> the kernel-level axiom audit, signature pinning, and the fresh-kernel
> `leanchecker` replay. The repository's Actions history records the most
> recent successful run.
> To inspect that state:
>
> ```text
> git fetch origin verified
> git checkout --detach origin/verified
> ```

A research library for finite models of groups and the rigidity,
operator-algebraic, combinatorial, and ring-theoretic structures that govern
them. The root module is `GroupApproximation.lean`; it imports the formal
library as a whole, while the subject directories provide smaller reading
paths.

The `verified` branch described above records the last completed public
audit. The paragraphs below describe the current source revision; publication of a new
verified pin is blocked until the exact claim manifest, full build, axiom
audit, fresh-kernel replay, and PDF provenance gate all pass for one commit.

## An explicit finitely presented CDE-MF obstruction

[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every
countable group is MF in the Carrión–Dadarlat–Eckhardt sense. Here MF means
embeddable as a group into the unitary group of an operator-norm matrix
corona

```text
∏ₙ M_{dₙ}(ℂ) / ⊕ₙ M_{dₙ}(ℂ).
```

Building this manuscript requires LaTeX2e dated 2025-06-01 or newer.  The
attested release PDF uses the `\DocumentMetadata{tagging=on}` interface
introduced in that release; the release workflow uses a digest-pinned TeX
Live 2026 image.

The current manuscript draft gives a literal finite presentation on eight
generators `v₁,v₂,v₃,x,y,z,t,c`. Its six-generator, twenty-relator base is used as a
presented group: no unproved identification with a semantic affine matrix
group is part of the argument. The stable letter doubles the three commuting
translation generators and fixes `x,y,z`; the involution `c` centralizes the
base. The defining relations make

```text
w = [tct⁻¹, v₁(tct⁻¹)v₁⁻¹]
```

a central element; its order-two relation follows from centrality and
`c² = 1` rather than being imposed separately. An explicit affine--Clifford
representation proves `w ≠ 1`. The manuscript proves property (T) by identifying
the twenty-relator base with `ℤ³ ⋊ SL₃(ℤ)` from the displayed presentation
and applying the classical affine-lattice theorem. Independently, the companion
derives the same property from its canonical rational P13 certificate and
the intrinsic fixed-point argument. These claims are not part
of the verified pin above until the full build, manifest, axiom, replay, and
PDF provenance gates all succeed at one commit.

The conceptual proof is organized around

```text
u = [tct⁻¹,v₁],       w = u².
```

The short reader-facing architecture, including the redundant-sign
presentation and the affine family, is recorded in
[`docs/BEAUTIFUL_NON_MF_PROOF_DESIGN_2026-08-14.md`](docs/BEAUTIFUL_NON_MF_PROOF_DESIGN_2026-08-14.md).

The reusable theorem is transport of the entire bounded asymptotic
commutant.  If `s iota(Γ) s⁻¹ <= iota(Γ)`, then property (T) and finiteness
turn the one-sided inclusion of fixed projections into equality, so every
compressor and its inverse preserve the asymptotic commutant.  For the marked
construction this makes `u` Hilbert--Schmidt trivial.  Cutting a separated
central sign to its negative corner then gives simultaneously `w = u² -> 1`
and `w -> -1`.  The finite-stage spectral-cut, polar-repair, and rank
calculations are the checked implementation of this short contradiction.

The paper also proves:

- the intrinsic all-compressors defect theorem: every finite normal subgroup
  of the compression--centralizer defect lies in the MF radical;
- an elementary finite-dimensional kill theorem over every field, requiring
  neither property (T), unitarity, nor centrality of the marked word;
- a cyclic-base comparison showing that exact finite-dimensional
  invisibility does not force the marked word to be trivial;
- a unital separable stably finite non-MF C*-algebra, namely `C*red(E)`;
- failure of closure of MF groups under quotients;
- the MF radical, its single-corona detector, and the largest MF quotient.

The paper additionally proves by a finite-coset-tower argument that the
Clifford witness is a finitely generated sofic non-MF group.  Thus the same
marked sign is MF-invisible but visible in both sofic and hyperlinear targets.
The abstract detector/radical implications are formalized in
`Sofic/RadicalSeparation.lean`; the concrete tower, finite-extension, and
sofic-by-amenable permanence proof is currently classified explicitly as a
paper-only claim in the numbered-claim manifest.

The result is specific to operator-norm approximation. It does not decide
whether the presenting group `E` itself is hyperlinear or sofic, or whether
`E/⟨w⟩` is MF, and does not address quasidiagonality of nuclear stably
finite C*-algebras.

### Formal counterpart

The conceptual headline is now
`KazhdanCliffordConstruction.kazhdanCliffordConstruction`: every finitely
presented property-(T) group with a proper injective endomorphism yields a
finitely presented non-MF extension.  The same theorem constructs the HNN--
Clifford representation, proves the base embeds, derives the marked sign's
square relation from centrality instead of imposing it, proves the sign is
nontrivial, and proves that every genuine norm-matrix C*-corona homomorphism
kills it.

The literal theorem is definitionally the same eight-generator presentation
and marked word as the manuscript. The affine--Clifford nontriviality witness,
canonical P13 tables and relator replays, the rotation quotient, the intrinsic
property-(T) bridge, Kazhdan transport, and the negative-corner obstruction are
joined by the zero-input declarations
`LiteralNonMFEndpoint.manuscriptTheoremA` and
`LiteralNonMFEndpoint.manuscriptTheoremD` in
`Sofic/LiteralNonMFEndpoint.lean`; the quantitative modules remain their
backend.
A revision is described as formally complete only after the headline theorem,
all exact wrappers, the signature roster, source scan, kernel audit, and fresh
replay pass at one commit.

The public CDE predicate and MF radical quantify literally over genuine
C*-coronas with natural matrix dimensions. Coordinate reindexing and polar
correction prove their equivalence to the internal unitary-sequence models.
For countable groups, the quotient by the radical is MF, is represented
faithfully in one corona, and has the expected universal factorization
property.

The internal definition permits any positive dimension sequence. The
Carrión--Dadarlat--Eckhardt convention requiring strictly increasing
dimensions is proved equivalent by a faithful cumulative block-diagonal
corona embedding; see `Sofic/OperatorMFIncreasingDimensions.lean`.

Reading path, front door first:

| Module | Role |
| --- | --- |
| `Sofic/KazhdanCliffordConstruction.lean` | General finitely presented Kazhdan self-embedding construction, HNN--Clifford witness, universal corona kernel, and non-MF endpoint |
| `Sofic/LiteralNonMFEndpoint.lean` | Hypothesis-free proof spine: `w = u²`, Kazhdan transport, the negative-corner contradiction, Clifford detection, and Theorems A and D |
| `Sofic/KazhdanAsymptoticCommutant.lean` | Transport of every bounded asymptotic-commutant sequence by every one-sided compressor and by the generated compression group |
| `Sofic/IntrinsicCompressionMFRadical.lean` | Intrinsic compression--centralizer defect and its finite-normal MF-radical theorem |
| `Sofic/ManuscriptKazhdanTransport.lean` | Natural-matrix-coordinate wrappers matching the two new manuscript theorems exactly |
| `Sofic/LiteralP13HodgeCertificate.lean` | Canonical rational P13 Hodge certificate assembled from exact residual blocks |
| `Sofic/LiteralBaseP13RotationQuotient.lean`, `Sofic/LiteralBaseP13PropertyTBridge.lean` | P13-to-rotation quotient and intrinsic literal-base bridge |
| `Sofic/ManuscriptExactWrappers.lean` | Shared exact outer-proposition wrappers for the generic retained claims |
| `Sofic/OperatorMF.lean` | Standard cofinite norm-matrix corona and `IsOperatorMF` |
| `Sofic/CDEOperatorMF.lean`, `Sofic/ActualCoronaMFRadical.lean` | Literal natural-dimension CDE predicate and genuine-corona radical |
| `Sofic/OperatorMFIncreasingDimensions.lean` | Equivalence with the strictly increasing dimension convention |
| `Sofic/MarkedCompressionSequentialKill.lean` | Universal kill theorem and direct `not_isOperatorMF` / `not_isWeakMF` obstructions |
| `Sofic/MarkedCompressionInclusionData.lean` | Exact one-sided compression interface; no injectivity or endomorphism hypothesis |
| `Sofic/NegativeCornerModel.lean`, `Sofic/ApproxInvolutionCorner.lean` | Involution rounding and negative-corner almost representations |
| `Sofic/KazhdanCompressorCorner.lean`, `Sofic/MarkedCompressionVectorChain.lean` | Adjoint Kazhdan projection, capture, and marked-word collapse |
| `Sofic/AdjointMatrix.lean`, `Sofic/ProjectionRankFlip.lean`, `Sofic/SpectralCapture.lean` | Finite-dimensional operator lemmas |
| `Sofic/MarkedCompressionGroup.lean`, `Sofic/CliffordLampGroup.lean`, `Algebra/MappingTelescope.lean` | Countable Clifford witness and nontrivial mark |
| `Sofic/NormMFResidualDetector.lean`, `Sofic/NormMFResidualFunctorial.lean` | Operator-norm MF residual and functoriality |
| `Sofic/NormMFUniversalCorona.lean`, `Sofic/NormMFCoronaRadical.lean` | Equivalence with the unitary-sequence corona radical and largest MF quotient |
| `Sofic/FiniteNormalCompressionObstruction.lean`, `Sofic/FiniteNormalCoronaObstruction.lean` | Finite-normal obstruction in ultraproduct and unitary-sequence corona language |
| `Sofic/LiteralNonMFPresentation.lean`, `Sofic/LiteralNonMFLinearWitness.lean` | Literal eight-generator presentation and exact nontrivial mark |
| `Criterion/FiniteDimensionalKill.lean`, `Sofic/LiteralFiniteDimensionalObstruction.lean` | Finite-dimensional obstruction over an arbitrary field, instantiated for the literal group |
| `Sofic/NormMFPrintedConsequences.lean`, `Sofic/NormMFResidualExactQuotient.lean` | Uniform invisibility, portability, and exact quotient factorization |
| `Sofic/OperatorMFPositiveControls.lean`, `Sofic/LiteralMFQuotientControls.lean` | Positive permanence results and exact `F₈ ↠ E` quotient nonclosure |
| `Analysis/FaithfulTracialMatrix.lean`, `Analysis/ProperIsometryFromCompression.lean` | Matrix-amplified faithful traces and the proper-isometry obstruction to stable finiteness |
| `Analysis/MaximalGroupCStar.lean`, `Analysis/ReducedGroupCStarMFObstruction.lean` | Concrete universe-relative maximal and reduced group C*-algebra consequences |

At a completed formal checkpoint, the headline declarations must be included
in the kernel audit roster with axiom closure restricted to `propext`,
`Classical.choice`, and `Quot.sound`; no literature theorem is introduced as a
Lean axiom.

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

## Trust and verification

The project pins Lean and Mathlib in `lean-toolchain` and `lake-manifest.json`.
GitHub Actions performs the computational checks:

- Lean Prover CI builds with warnings as errors, runs source and compiled
  environment scans, checks transitive axiom closures, pins mapped theorem
  signatures, and replays compiled objects through a fresh Lean kernel.
- The non-MF and property-(TT)/T PDF workflows validate visible TeX-to-formal
  references, compile and lint each manuscript, reject unresolved references
  and layout overflow, render every page, validate the PDFs, and publish
  immutable, attested artifacts for audited revisions.
- Independent kernel re-check is an additional manually triggered audit.
- API documentation publishes the generated Lean documentation.

The accepted axiom closure is restricted to `propext`, `Classical.choice`,
and `Quot.sound`. The audit rejects `sorry`, project axioms, compiler-trust
shortcuts, and theorem-shaped literature assumptions.

Key audit files:

- `scripts/check.py`: source-level checks;
- `scripts/Audit.lean`: statement pins, axiom closure, and environment scans;
- `GroupApproximation/Endpoint/LiteralNonMFAudit.lean`: planned focused audit
  of the literal eight-generator endpoint and its manuscript wrappers;
- `scripts/Signatures.lean` and `docs/CLAIM_SIGNATURES.md`: elaborated public
  signatures;
- `scripts/check_non_mf_refs.py` and `scripts/check_property_tt_refs.py`:
  visible manuscript-to-Lean reference checks;
- `docs/PROPERTY_TT_CLAIM_MAP.md`: statement mapping for the property-(TT)/T
  paper.

Cold local builds are expensive. The maintained verification path is the
GitHub Actions workflows in `.github/workflows/`.
