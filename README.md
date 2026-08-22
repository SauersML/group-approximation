# Group Approximation

The remote `verified` branch is automatically fast-forwarded after every complete Lean Prover CI success on `main`. Use that for the most recent correct Lean code.

## A non-MF group
[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every
countable group is MF in the Carrión–Dadarlat–Eckhardt sense. Here MF means
embeddable as a group into the unitary group of an operator-norm matrix
corona

```text
∏ₙ M_{dₙ}(ℂ) / ⊕ₙ M_{dₙ}(ℂ).
```

The main article is available as
[`non_mf_groups_exist.pdf`](non_mf_groups_exist.pdf) and as a navigable
[web edition](https://sauersml.github.io/group-approximation/paper/).
Further results and variants are collected separately in
[`non_mf_group_notes.tex`](non_mf_group_notes.tex), with a
[`PDF`](non_mf_group_notes.pdf) and a dedicated
[notes web edition](https://sauersml.github.io/group-approximation/notes/).

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

## The Lean formalization

The Lean code is organized as a reusable library, not as a proof script for
one result.  Definitions and theorems are stated at their natural level of
generality; concrete presentations and finite certificates are downstream
instances of those interfaces.  Import [`GroupApproximation.lean`](GroupApproximation.lean)
for the whole library, or import a narrower module for a smaller dependency
closure.

| Area | Main directories | Reusable contents |
| --- | --- | --- |
| Group constructions | `Algebra/`, `GroupTheory/`, `Higman/`, `Covers/`, `Monsters/` | Presentations, normal forms, free products, HNN extensions, quotients, embeddings, and torsion arguments |
| Finite approximation | `Sofic/`, `Criterion/`, `Stability/`, `Domination/`, `Matching/` | MF, sofic, and hyperlinear interfaces; finite models; residuals; ultraproducts and matrix coronas; permanence and obstruction principles |
| Rigidity | `PropertyT/`, `Kazhdan/`, `PropertyTT/` | Fixed-point formulations, relative property (T), Kazhdan and Hodge certificates, spectral gaps, and property (TT)/T |
| Analysis and operator algebra | `Analysis/`, `KOne/`, `Leavitt/`, `Steinberg/` | Matrix estimates, projections, traces, C*-algebra constructions, K-theory interfaces, and noncommutative ring models |
| Combinatorial and quantum groups | `Kun/`, `KunThom/`, `Quantum/` | Graph and permutation constructions, approximation mechanisms, and quantum-group infrastructure |
| Verification and public API | `Endpoint/`, `Meta/`, `Computability/`, `Manuscript/` | Stable exports, exact finite-certificate replay, computability wrappers, statement matching, and axiom audits |

The `Literal*` modules provide fully specified examples and machine-checkable
certificate data.  They are kept separate from the generic layers so that
other projects can reuse the definitions, permanence theorems, and proof
machinery without importing a particular presentation.

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
