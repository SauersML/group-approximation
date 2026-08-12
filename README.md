# Group Approximation

A Lean 4 research library for finite models of groups and the rigidity,
operator-algebraic, combinatorial, and ring-theoretic structures that govern
them.

The project is not organized around one theorem or one paper. It contains
several interacting developments:

- sofic, LEF, hyperlinear, and matrix approximation;
- Kazhdan property (T), explicit Kazhdan systems, and fixed-point methods;
- expander decomposition and repair arguments;
- matching, finite groupoids, and local-to-global approximation criteria;
- elementary and Steinberg groups over noncommutative rings;
- Leavitt algebras, matrix self-similarity, unstable elementary reduction,
  and Whitehead K_1;
- quasi-cocycles and property (TT)/T;
- domination, representation-theoretic obstructions, and finitely presented
  covers.

The root module is GroupApproximation.lean. It imports the formal library as a
whole; individual subject directories provide more manageable reading paths.

## Current paper

property_tt_leavitt.tex develops one part of the library: fixed-coordinate
matrix factorization and property (TT)/T over finite-type noncommutative
rings. Its principal new application is property (TT)/T for the unit group of
the binary Leavitt algebra.

Every numbered result in that paper links visibly to a public Lean
declaration. The paper also gives a proof-order guide showing how the formal
proof is assembled. Its public formal surfaces are:

| Module | Role |
| --- | --- |
| PropertyTT/PaperStatements.lean | Statement-level interface for the paper |
| PropertyTT/LocalizedComplexPlane.lean | Homogeneous finite-control plane estimate |
| PropertyT/FreeRootCharacterValuation.lean | Finite Fourier transport and boundary limits |
| PropertyTT/FiniteTypeLeavittTT.lean | Rank-four assembly and all-ranks transport |
| KOne/PaperStatements.lean | Rank-two elementary diagonal endpoint |
| KOne/AllRanksElementaryCore.lean | All-ranks GL=E over the binary Leavitt algebra |

The paper uses the published K-theoretic proof of K_1=0 and GL_n=E_n for the
binary Leavitt algebra. Lean reaches the same endpoint independently through
the constructive prefix-code pencil reduction in KOne/. The manuscript names
that formal route explicitly; external results are not smuggled into Lean as
axioms.

The earlier standalone nonsofic manuscript has been removed. The current
property (TT)/T paper neither states nor depends on a nonsoficity corollary.
The repository still contains broader soficity and nonsoficity developments
as part of the formal library.

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

The project pins Lean and Mathlib in lean-toolchain and lake-manifest.json.
GitHub Actions performs the computational checks:

- Lean Prover CI builds with warnings as errors, runs source and compiled
  environment scans, checks transitive axiom closures, pins mapped theorem
  signatures, and replays compiled objects through a fresh Lean kernel.
- Build and commit property TT PDF validates TeX-to-Lean references, compiles
  and lints the current paper, rejects unresolved references and layout
  overflow, renders every page, validates the PDF, and commits it to main.
- Independent kernel re-check is an additional manually triggered audit.
- API documentation publishes the generated Lean documentation.

The accepted axiom closure is restricted to propext, Classical.choice, and
Quot.sound. The audit rejects sorry, project axioms, compiler-trust
shortcuts, and theorem-shaped literature assumptions.

Key audit files:

- scripts/check.py: source-level checks;
- scripts/Audit.lean: statement pins, axiom closure, and environment scans;
- scripts/Signatures.lean and docs/CLAIM_SIGNATURES.md: elaborated public
  signatures;
- scripts/check_property_tt_refs.py and docs/PROPERTY_TT_CLAIM_MAP.md:
  statement mapping for the current paper.

Cold local builds are expensive. The maintained verification path is the
GitHub Actions workflows in .github/workflows/.
