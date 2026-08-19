# Palomar registry code audit (eight entries, fourteen repositories)

Date: 2026-08-19.  Constraint, as for `EXTERNAL_CODE_AUDIT.md`: no lake
dependency outside Mathlib, no wholesale vendoring, individual results only,
with attribution in the file header in the form
`GroupApproximation/Meta/BatchedKernelChecks.lean` already uses.

## What was audited

Every Lean entry then in the Palomar registry (`palomar-registry.org`), read at
the commit each entry pins.  The registry is a SPA; the records are served as
JSON from `data.palomar-registry.org/entries/<id>-v<n>.json`, and each record
pins the submission commit, the substantive library behind it, and the whole
transitive dependency set, mirrored under the `PalomarArchive` org.

| Entry | Repository @ pin | Result |
| --- | --- | --- |
| PALOMAR-2026-08-08-000001 v3 | `kim-em/erdos-unit-distance-comparator` @ `be6c2ee4` (+ `kim-em/erdos-unit-distance` @ `34b4587b`) | the uniform-constant form of Erdős's unit-distance conjecture is false (Alpöge) |
| PALOMAR-2026-08-17-000001 | `rkirov/jordan_pick` @ `ccbcc614` | Radó: a Riemann surface is second countable |
| PALOMAR-2026-08-17-000002 | `Paul-Lez/hadamard-668-comparator` @ `da94bc80` | an explicit order-668 Hadamard matrix |
| PALOMAR-2026-08-17-000003 | `gexahedron/sabidussi-lean` @ `58307d74` | Sabidussi compatibility for Euler tours |
| PALOMAR-2026-08-17-000004 | `jaumededios/cantor-frames-palomar` @ `e1ce0152` (+ `Cantor_Measure_Frames` @ `f9b80c7e`) | no Fourier frame exists for Cantor measures |
| PALOMAR-2026-08-18-000001 | `LionSR/LDT-comparator` @ `15f1d5b2` (+ `LionSR/MIPStarRE` @ `892b939c`) | quantum soundness of the low individual degree test — the core of MIP\* = RE |
| PALOMAR-2026-08-18-000003 | `xinjiegit/ben_27_formalization` @ `f7035296` | `m(p) ≥ c (log p / log log p)²` for no-unique-sum sets in `𝔽_p` |
| PALOMAR-2026-08-19-000001 | `rkirov/jordan_pick` @ `b3c9b7cf` | the Jordan curve theorem, with Brouwer built from scratch |

Also read, as the tooling behind those entries: `kim-em/leancert`,
`b-mehta/PrimeCert`, `hanwenzhu/LeanArchitect`, `FormalFrontier/TauCeti`.

## Licence finding, recorded first because it constrains everything below

**`LionSR/MIPStarRE` and `jaumededios/Cantor_Measure_Frames` carry no licence
file.**  Their comparator *wrappers* are Apache-2.0, and the generated
`Challenge.lean` in `LDT-comparator` is therefore usable, but the libraries and
the generator scripts are not.  Nothing is copied from either.  Where an idea
of theirs is used it is cited as prior art and written here from scratch, and
the file that does so says so.

Everything else is Apache-2.0 except `b-mehta/PrimeCert`, which is MIT.

## Outcome: three ports, one measurement, and a documented list of passes

The bar was the same as the physlib audit: not already available here, consumed
by live or imminent work, and worth more than its length.  Three things cleared
it.

### 1. `#audit_axioms` — `GroupApproximation/Meta/AxiomGuard.lean`

From `gexahedron/sabidussi-lean` (Apache-2.0), whose `Sabidussi/Audit.lean`
pins each audited theorem with `#guard_msgs in #print axioms`, so that a
widened axiom closure is a **compile error**; and from
`FormalFrontier/TauCeti`'s `Scripts/Axioms.lean` (Apache-2.0), which carries
the same three-axiom allowlist plus the rule that governance tooling must fail
loudly rather than pass vacuously (it errors if it audited zero declarations).

What this repository had was 511 bare `#print axioms` lines across
`Endpoint/Audit.lean`, `Endpoint/ChosenNonMFAudit.lean` and
`Domination/Audit.lean`: a report written into the build log that then
succeeded whatever it found.  The gate existed only in `scripts/Audit.lean`,
which is a separate CI step — and a separate step is what a `continue-on-error`,
a cancelled run or a reordering removes quietly.  All 511 are now
`#audit_axioms`, which prints the identical report and throws unless the
closure is inside `{propext, Classical.choice, Quot.sound}`.  Both directions
are calibrated in the defining module.

Not copied: a `#guard_msgs` fixture pins the *rendering* of the report,
including Lean's line-wrapping choices, and 511 of those would be 511
line-wrapping decisions to keep true.  TauCeti's whole-library sweep is not
ported either — it uses `unsafe Lean.withImportModules`, which this
repository's source scan forbids outright, and `scripts/Audit.lean`'s
`Audit.Scan.corpusNames` already filters by defining module rather than by name
prefix, so the coverage gap TauCeti's design closes is not open here.

### 2. Audit-surface measurement — `scripts/StatementClosure.lean`

From the `leanprover/comparator` protocol that every Lean entry in the registry
uses: the entire human audit surface is one `Challenge.lean` that imports only
Mathlib and states the theorem with `sorry`; a mechanical check then certifies
that the library proves exactly that statement from the standard axioms, so a
reader who agrees the challenge says the right thing need read nothing else.
The registry grades how small that file is — 8 lines for the Jordan curve
theorem, and 805 lines flagged as "exceeds the preferred audit surface" for the
low-degree test.

We cannot state soficity, the MF radical or the compression defect in Mathlib
alone, so a `Challenge.lean` here would be the closure of our own definitions
reachable from a statement.  `scripts/StatementClosure.lean` computes exactly
that closure and writes the counts to `metadata/AUDIT_SURFACE.md`, gated for
drift in `prover.yml` beside the signature snapshots.  First measurement: 1186
local constants and 7737 source lines over all 531 mapped declarations;
`BooneGroup.exists_finitelyPresented_wordProblem_undecidable` needs zero, being
already stated in Mathlib's vocabulary, and `manuscriptTheoremA` needs 108
constants and 464 lines.

The extraction design is prior art from `LionSR/MIPStarRE`'s
`scripts/comparator/extract_closure.lean`.  Unlicensed, so written here; and it
answers a deliberately different question — what a statement *means* (unfold
definitions, do not traverse proofs) rather than what the kernel closure is,
which is `scripts/Audit.lean`'s job.

**Not adopted: running comparator itself.**  Its sandbox is `landrun`, which
needs Landlock (kernel ≥ 5.13); the compute nodes have neither Landlock nor a
user systemd bus, so it would have to be a GitHub Actions job.  The
kernel-replay half of the protocol already exists here as
`.github/workflows/independent-kernel.yml` (`lean4export` + `nanoda`); what was
missing was the statement-comparison half, and the closure measurement is its
first step.  Three escape hatches recorded for whoever finishes the job:
comparator ships a `fake-landrun` development stub for non-Linux;
`LDT-comparator`'s `verify.sh` flips `enable_nanoda` off with `jq` in that
mode; and `cantor-frames-palomar`'s `scripts/landrun_passthrough.py` works
around landrun's CLI consuming the first `--`, which comparator's `lean4export`
invocation needs.

### 3. Consistency is closeness — `GroupApproximation/Sofic/ConsistencyDistance.lean`

The one piece of *mathematics* that cleared the bar.  From Section 4 of
Ji–Natarajan–Vidick–Wright–Yuen, *Quantum soundness of the classical low
individual degree test* (arXiv:2009.12982), the paper `MIPStarRE` formalizes:
the whole soundness argument there is carried in two numbers attached to a pair
of outcome families — the mass they place on *disagreeing* outcomes, and the
state-dependent distance between them — and its first move is that for
projective families these are the same number up to a factor of two.

That is exactly the exchange rate the `hyperlinear-implies-sofic` cluster is
missing.  Every live route in it turns a hypothesis of the first kind (a table
has small multiplicative defect; a test sees agreement) into a conclusion of
the second (the operators are close, so they can be rounded).  The module
proves it in the tracial setting: `Y` a finite model, `τ` its normalized trace,
`sdDistSq = 2·consDefect` for projective families and `≤` for effects, with the
quadratic triangle rule a chain of rounding steps consumes, and with the
classical instance that the consistency defect of two readout measurements is
the normalized Hamming distance.  Research graph:
`research/consistency-defect-is-state-dependent-distance.md`.

`MIPStarRE` is unlicensed, so nothing is copied; and the tracial setting is not
theirs — theirs is a vector state on a bipartite space, and the substitution is
what makes the classical instance land on the microstates of `Sofic.Sofic`
rather than on a translation of them.  The effect inequality `τ(E²) ≤ τ(E)` is
proved from `E − E² = E(1−E)E + (1−E)E(1−E)`, a sum of two congruences of
positive semidefinite matrices, so it needs no square root, no spectral theorem
and no functional calculus — which keeps it clear of the CFC instance tower
that `instance-cost-abbrev-towers` records as expensive here.

## Passes, with reasons

| Target | Where | Why not |
| --- | --- | --- |
| Naimark dilation of a POVM to a PVM, with correlation preservation | `MIPStarRE/LDT/MakingMeasurementsProjective/Naimark*.lean` | genuinely wanted — it is the shape of the open `simultaneous-dilation-splice` — but unlicensed and large, and our Stinespring lane already dilates on `A →₀ H`.  Recorded as the thing to write next, not to copy |
| orthonormalization: strongly self-consistent ⇒ close projective, with a `100ζ^(1/4)` envelope | `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean` | the actual content of a rounding theorem, and the analogue of what `traffic-branching-rounding-hierarchy` and `definetti-group-table-rounding` need.  Unlicensed; and its hypotheses (permutation-invariant bipartite state) are not ours.  The right move is to state our own, in the metric now available |
| finite conic duality: separating functional, primal = dual over the PSD cone | `MIPStarRE/Quantum/FiniteConicDuality.lean`, `FiniteMatrix/Order.lean` | the natural home for `group-table-cpsd-cp-face-collapse`, whose refutation form asks for exactly one exposed functional.  Unlicensed; and Mathlib's `ProperCone` separation is the better base to build it on when that claim is attacked |
| projector spectral decomposition, subprojector algebra, `trace = rank` | `MIPStarRE/Quantum/ProjectorONB.lean` | unlicensed, and the overlapping half is already here (`ProjectionRankFlip`, `SpectralCapture`, `ApproxInvolutionCorner`) |
| `BitVec` packing + `decide +kernel` for a large explicit object | `Paul-Lez/hadamard-668-comparator` `Solution.lean` | the recipe is right and we already use `decide +kernel` at 255 sites, but its other half is `set_option maxRecDepth 10000`, which this repository's source scan forbids.  A port would have to shard instead, which is what `Meta/BatchedKernelChecks.lean` already does |
| circulant algebra with the inversion permutation (`R S(x) = S(x)ᵀ R`, Goethals–Seidel array) | same | clean and Apache-2.0, but it buys nothing until an atlas certificate is actually stated over a cyclic Fourier corner; recorded as a pointer |
| reduction mod `p` of an integer lattice, `p ∣ every maximal minor ⇒ rank drop` | `xinjiegit/ben_27_formalization` `NUSLean/CollisionLattice.lean` | Apache-2.0 and genuinely adjacent to `coherent-configuration-orbital-rounding` and `iwahori-fractional-transport-integralization`; passes only because neither claim has a Lean statement yet to consume it.  Revisit when one does |
| parity counting: odd solution count ⇒ existence | `gexahedron/sabidussi-lean` `OddBalance.lean` | Apache-2.0; the technique is standard and the specific statements are about Euler tours.  No consumer |
| Brouwer from covering-space lifting, `π₁(S¹) ≅ ℤ`, no-retraction, nearest-point projection | `rkirov/jordan_pick` `JordanCurve/Brouwer.lean` | Apache-2.0 and self-contained, but nothing here is a fixed-point argument |
| Haar system on a `b`-adic Cantor group, sampling inequality sandwich, `F` scaling identity | `jaumededios/Cantor_Measure_Frames` | unlicensed; and the frame-theoretic impossibility shape, while structurally like ours, has no live consumer |
| multiquadratic fields, norm fibres, ideal-class pigeonhole | `kim-em/erdos-unit-distance` | Apache-2.0; number theory with no contact surface here |
| Pocklington certificate ladder: registry attribute, `PrimeDict`, `prime_cert%` elaborator, Python generator | `b-mehta/PrimeCert` | MIT.  The *architecture* is the right one for the atlas certificates — search outside Lean, kernel-check a compact certificate, trust only a soundness theorem — and is recorded as the model to follow.  The primality-specific code has no use here |
| interval-arithmetic "Golden Theorems": `checker = true → ∀ x ∈ I, f x ≤ c` | `kim-em/leancert` | Apache-2.0.  The obvious tool for `effective-transport-modulus` and any explicit numerical modulus.  Passes only because no such modulus is currently being proved; the first one should use it rather than `nlinarith` |
| `@[blueprint]`: generate the LaTeX node from Lean, with `uses` / `proofUses` / `sorry_using` | `hanwenzhu/LeanArchitect` | Apache-2.0.  It inverts our `\leanstep` contract — the prose would be *derived* from Lean and so could not drift — which would retire the `manuscript-cuts-orphan-docstrings` defect class.  A real project, not a port; recorded as a design direction |
| `formalization.yaml` v0.4 (mathlib-initiative provenance schema) | every entry | not code.  Worth adopting in `metadata/`: `kim-em/erdos-unit-distance-comparator`'s copy is the model, with `scope_limitations` volunteering that the work is neither first nor strongest, `related_formalizations` distinguishing conditional from unconditional, `fidelity.divergences` naming a sorried dependency and then proving it outside the axiom closure, and `review.status: self-assessed` stating that machine-checking is not a check on whether the statement is the right formalization |

## What the registry's own grading says about us

A record's `trust` block is a function of how small the challenge file is:
`challenge_bytes`, `challenge_lines`, `challenge_imports`, and whether every
dependency is allowlisted.  Seven of the eight entries import Mathlib and
nothing else and carry no `reasons`; the eighth, at 805 lines, is flagged.
`metadata/AUDIT_SURFACE.md` is the same number for this development, computed
the same way, and is now a gated file.
