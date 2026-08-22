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

The `verified` branch described above records the last completed public proof
audit. The paragraphs below describe the current source revision; publication
of a new verified pin is blocked until the exact claim manifest, full build,
axiom audit, signature pinning, and fresh-kernel replay all pass for one
commit. Separate release workflows build and attest the PDFs from an exact
prover-certified source revision.

## A non-MF group

[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every
countable group is MF in the Carrión–Dadarlat–Eckhardt sense. Here MF means
embeddable as a group into the unitary group of an operator-norm matrix
corona

```text
∏ₙ M_{dₙ}(ℂ) / ⊕ₙ M_{dₙ}(ℂ).
```

Building this manuscript requires LaTeX2e dated 2025-06-01 or newer, and
the release and draft workflows both compile inside the same digest-pinned
TeX Live **2025** image (`TEXLIVE_IMAGE` in
`.github/workflows/build-non-mf-pdf.yml`, `draft-non-mf-pdf.yml` and
`refresh-non-mf-pdf.yml`).  The 2026 image is deliberately not used: its
`tagpdf` aborts at `\tableofcontents` on this source and garbles the
contents page.  The header comment at the top of the manuscript records the
same constraint.

Tagging is **enabled**: the source sets
`\DocumentMetadata{lang=en-US,pdfversion=2.0,tagging=on}`, and the TikZ
figure carries alternative text inside a `Figure` structure element, so
a LuaLaTeX build produces `/MarkInfo`, `/StructTreeRoot`, and an `/Alt`
entry for the figure — what the release workflow's `Tagged: yes`
assertion requires.  Two limits are worth naming.  `tagpdf` reports that
math tagging is running without `unicode-math`, which this manuscript
does not load, and the theorem environments and margin notes are tagged
as ordinary paragraphs, so the structure tree is coarser than the
document's logical structure.  The committed PDF predates the change and
stays untagged until the next release build.

The current manuscript draft gives a literal finite presentation on eight
generators `v₁,v₂,v₃,x,y,z,t,c`. Its six-generator, twenty-relator base is
identified from its displayed presentation with `ℤ³ ⋊ SL₃(ℤ)`. The stable
letter doubles the three commuting
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
the intrinsic fixed-point argument. These claims are not part of the verified
pin above until the full build, manifest, axiom, signature, and fresh-kernel
replay gates all succeed at one commit.

The conceptual proof is organized around

```text
u = [tct⁻¹,v₁],       w = u².
```

The reusable theorem is transport of the entire bounded asymptotic
commutant.  If `s iota(Γ) s⁻¹ <= iota(Γ)`, then property (T) and finiteness
turn the one-sided inclusion of fixed projections into equality, so every
compressor and its inverse preserve the asymptotic commutant.  For the marked
construction this makes `u` Hilbert--Schmidt trivial.  Cutting a separated
central sign to its negative corner then gives simultaneously `w = u² -> 1`
and `w -> -1`.  The manuscript uses the shorter finite-norm-ultraproduct
proof; the formal backend also supplies the spectral-cut and polar-repair
lemmas needed to return from corners to positive matrix coordinates.

The paper also proves:

- the intrinsic all-compressors defect theorem: every finite normal subgroup
  of the compression--centralizer defect lies in the MF radical;
- an elementary finite-dimensional kill theorem over every field, requiring
  neither property (T), unitarity, nor centrality of the marked word;
- a cyclic-base comparison showing that exact finite-dimensional
  invisibility does not force the marked word to be trivial;
- a unital separable stably finite non-MF C*-algebra, namely `C*red(E)`;
- soficity of `E` itself, so that a finitely presented sofic and hyperlinear
  group need not be MF;
- non-MF of the quotient `E/⟨w⟩`, so that `{1, w}` is a proper subgroup of the
  MF radical of `E`;
- the exact paper-level computation
  `Res_MF(E) = ⟨⟨[tct⁻¹,v₁]⟩⟩`, with MF universal quotient identified as
  `Σ *_B (B × C₂)`;
- a torsion-free finitely presented non-MF group, obtained at paper level by
  combining the normal-Kazhdan obstruction with the Fournier-Facio--Hull--Osin
  small-cancellation construction;
- failure of closure of MF groups under quotients;
- the MF radical, its single-corona detector, and the universal MF quotient;
- a finite universal Horn obstruction and a nonempty clopen cylinder of
  non-MF eight-marked groups;
- a dimension-independent finite test set and positive defect threshold
  forcing the literal mark within operator norm `< 1` of the identity.

The result is specific to operator-norm approximation. Soficity of `E` and
non-MF of `E/⟨w⟩` are proved by separate arguments, the first from the block
normal form and the second from orbit collapse; the operator-norm obstruction
by itself decides neither, and none of this addresses quasidiagonality of
nuclear stably finite C*-algebras.

Kazhdan transport is a rigidity mechanism, not a new fourth approximation
class alongside MF, sofic, and hyperlinear groups.  The present result is an
operator-norm obstruction and makes no additional sofic or hyperlinear
classification claim.

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
| `Sofic/NormMFUniversalCorona.lean`, `Sofic/NormMFCoronaRadical.lean` | Equivalence with the unitary-sequence corona radical and universal MF quotient |
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

**What the verification does and does not claim.** Two different statements
are checked by two different artefacts, and they are not interchangeable.
Every numbered claim of the manuscript has a Lean declaration whose
proposition is that claim: `scripts/check_non_mf_claim_manifest.py`,
`check_non_mf_refs.py` and `check_non_mf_zero_input.py` gate that, and the tree
contains no `sorry` and no project axiom. The *prose proofs* are a separate
question, tracked step by step in
[`metadata/NON_MF_PROOF_LEDGER.md`](metadata/NON_MF_PROOF_LEDGER.md); at the
current revision that ledger grades 437 steps.  In the statement column, 404
are `EXACT`, three are `MISMATCH`, and 30 are `MISSING`; in the proof column,
404 are `EXACT`, one is a `MISMATCH`, and 32 are `MISSING`.
Thus "every numbered result has a checked formal counterpart" is accurate
while "the manuscript proof has been formalized line by line" is not.  In
particular, the quotient-presentation and Shulman-amalgam argument computing
`Res_MF(E)`, and the Fournier-Facio--Hull--Osin small-cancellation input for
the torsion-free example, are paper-level mathematics rather than Lean
theorems. The ledger is also a *correspondence* audit, by its own stated policy: it
asks whether Lean says what the manuscript says, and classifies every
discrepancy as a Lean-side or matching issue. It is not an adversarial referee
of the mathematics, and no claim here should be read as one.

## Property (TT)/T and the binary Leavitt algebra

`PropertyTT/` develops fixed-coordinate matrix factorization and property
(TT)/T over finite-type noncommutative rings. Its principal application is
property (TT)/T for the unit group of the binary Leavitt algebra. Its main
formal surfaces are:

| Module | Role |
| --- | --- |
| `PropertyTT/PaperStatements.lean` | Statement-level interface |
| `PropertyTT/LocalizedComplexPlane.lean` | Homogeneous finite-control plane estimate |
| `PropertyT/FreeRootCharacterValuation.lean` | Finite Fourier transport and boundary limits |
| `PropertyTT/FiniteTypeLeavittTT.lean` | Rank-four assembly and all-ranks transport |
| `KOne/PaperStatements.lean` | Rank-two elementary diagonal endpoint |
| `KOne/AllRanksElementaryCore.lean` | All-ranks `GL = E` over the binary Leavitt algebra |

`K₁ = 0` and `GLₙ = Eₙ` for the binary Leavitt algebra are published
K-theoretic results. Lean reaches the same endpoint independently through the
constructive prefix-code pencil reduction in `KOne/`; external results are not
imported as axioms.

## Nonsofic groups exist

The construction the library is named after is `EL₄(L_{𝔽₂}(1,2))`: the rank-four
elementary group over the universal binary Leavitt algebra, is countable,
infinite, finitely generated, has property `(T)`, and is not sofic. Its
endpoints are in `Endpoint/MainResults.lean` — `nonsofic_groups_exist`,
`countable_nonsofic_groups_exist`, `exists_finitelyPresented_nonsofic_group`,
and `countable_group_without_essentiallyFreeNearAction_exists`, the negative
answer to Pestov's Question 5.3 — and each printed statement has one endpoint
of its own in `Endpoint/ManuscriptStatements.lean`. The statement-by-statement
correspondence is [`notes/CLAIM_MAP.md`](notes/CLAIM_MAP.md), generated from the
margin notes of the manuscript and checked by `scripts/check.py`.

The manuscript itself is no longer kept in the repository; the Lean endpoints
above are the primary record, and `scripts/check.py` reports the absence rather
than passing silently over it.

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

The notes/ directory is a working research archive as well as documentation.
Files prefixed FALSE_ record investigated approaches that were ruled out;
they are retained so failed routes and their precise obstructions remain
searchable.

## The Palomar registry entry

The repository carries a
[Palomar](https://palomar-registry.org) submission surface: `Palomar/Challenge.lean`
states one theorem against Mathlib alone, `PalomarSolution.lean` proves the
same statement from this development, and `Palomar/comparator.json` selects it.
`notes/PALOMAR_SUBMISSION.md` is the record: what the entry claims, what it
deliberately does not, and how to verify it.

The compared declaration is
`ExplicitNonMF.explicit_fp_sofic_hyperlinear_not_MF`.  For the explicit
eight-generator, forty-one-relator group `E` and its distinguished word
`w = [tct⁻¹, v₁(tct⁻¹)v₁⁻¹]` it states that `E` is finitely presented and
six-generated, that `w` is a nontrivial central involution, that `E` is sofic
and hyperlinear, that every operator-norm asymptotic unitary representation
sends `w` to the identity -- uniformly, for one defect budget on one finite
test set, in every dimension -- that `E` is therefore not MF, and that every
finite-dimensional representation over every field and every homomorphism to a
finite group kills `w` as well.

Everything else the manuscript proves -- the reduced and maximal group
C*-algebra statements, the hyperlinear non-MF trace, the non-MF quotient by
`w`, the general obstruction criteria, the undecidability of MF recognition --
is proved in this repository but is **not** part of that Comparator selection
and is not verified by that entry.

## Trust and verification

The project pins Lean and Mathlib in `lean-toolchain` and `lake-manifest.json`.
GitHub Actions performs the computational checks:

- Lean Prover CI builds with warnings as errors, runs source and compiled
  environment scans, checks transitive axiom closures, pins mapped theorem
  signatures, and replays compiled objects through a fresh Lean kernel.
- The non-MF PDF workflow validates visible TeX-to-formal references, compiles
  and lints the manuscript, rejects unresolved references and layout overflow,
  renders every page, validates the PDF, and publishes immutable, attested
  artifacts for audited revisions.
- Independent kernel re-check is an additional manually triggered audit.
- API documentation publishes the generated Lean documentation.

The accepted axiom closure is restricted to `propext`, `Classical.choice`,
and `Quot.sound`. The audit rejects `sorry`, project axioms, compiler-trust
shortcuts, and theorem-shaped literature assumptions.

Key audit files:

- `scripts/check.py`: source-level checks;
- `scripts/Audit.lean`: statement pins, axiom closure, and environment scans;
- `GroupApproximation/Endpoint/ChosenNonMFAudit.lean`: fast focused axiom audit
  of the chosen non-MF endpoint, together with the part of the literal
  eight-generator presentation that is unconditional;
- `scripts/Signatures.lean` and `metadata/CLAIM_SIGNATURES.md`: elaborated public
  signatures;
- `scripts/check_non_mf_refs.py`: visible manuscript-to-Lean reference checks;
- `scripts/check_non_mf_zero_input.py`: enforces that every Lean declaration
  cited by the non-MF manuscript has no declaration inputs (all quantifiers
  occur inside the proposition);
- `notes/NON_MF_IMPACT_FORMAL_STATUS.md`: records which stronger consequences
  have closed Lean endpoints and which still use literature or require new
  mathematics.

Cold local builds are expensive. The maintained verification path is the
GitHub Actions workflows in `.github/workflows/`.

### Citation policy

The manuscript prefers original journal articles, version-pinned preprints,
and stable OAI-hosted papers. Authoritative scholarly books and monographs are
also acceptable when they are the clearest or canonical source and the
citation identifies an exact theorem, section, or page. Talks may be cited for
claims whose relevant source is genuinely a talk or for historical
attribution. A secondary source should not replace an available primary source
for a load-bearing mathematical claim.
