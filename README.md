# Group Approximation

The remote `verified` branch is automatically fast-forwarded after every complete Lean Prover CI success on `main`. Use that for the most recent correct Lean code.

## A non-MF group

[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every group is MF. [`non_mf_group_notes.tex`](non_mf_group_notes.tex) is an archived research notebook for an earlier construction and is not a companion to the current manuscript.

[`non_mf_groups_exist.pdf`](non_mf_groups_exist.pdf) at the repository root is the distribution PDF, rebuilt from the root TeX source by the draft PDF workflow. The obsolete duplicate under `output/pdf/` has been removed. A draft PDF build does not certify the manuscript's Lean coverage.

The manuscript does not yet have complete sentence-level Lean coverage. The
[current census](metadata/NON_MF_SENTENCE_CENSUS.md) records the gaps, and the
[repair status](metadata/NON_MF_REPAIR_STATUS.md) distinguishes the corrected
statements and tested proofs from the remaining verification work.

[A direct rational-certificate proof](research/artifacts/affine-clifford-direct-non-mf-proof-2026-09-08.md)
constructs an explicit nine-generated non-MF group and proves that every norm
matrix corona representation kills its nontrivial central sign. Its two
appendices derive the needed uniform spectral estimate from an integer
certificate, without invoking a property-(T) theorem. The independent
standard-library checker passed on MSI in 0.45 seconds. The
[Cairn claim](research/affine-clifford-non-mf-from-rational-certificate.md)
records the proof and its scope; this written argument has no new Lean
formalization claim.

## Research notes

[The Jacobson two-braid reduction](research/artifacts/jacobson-two-braid-reduction-2026-09-07.md)
gives an explicit marked candidate and proves that its mark is MF-invisible
exactly when one matrix infimum is positive. The finite-packet reductions,
sharp rank restrictions, and an [exact mixed example](research/artifacts/jacobson-mixed-packet-certificate-2026-09-07.md)
are integrated with Cairn and have executable arithmetic checks. The
positive lower bound and the Jacobson property-(T)-free existence goal remain open.

[Cyclic attachments for one-relator groups](research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md)
give written soficity proofs for all nested Baumslag presentations with
conjugator `w=b^p a^s b^q`, including the asymmetric example asked about in
Berlai's paper, and for a broader family with one-sided indexed support.
The proofs and their dependencies are integrated into Cairn. The general
one-relator question remains open here, and these results are not Lean-certified.

[A noisy direction counterexample](research/artifacts/unique-games-noisy-direction-counterexample-2026-09-07.md)
refutes the proposed affine glue lemma in the Unique Games research track.
The proof and [exact replay](scripts/check_unique_games_noisy_direction.py)
are integrated with Cairn; UGC remains open. Reproduce with
`python3 scripts/check_unique_games_noisy_direction.py --check`.

[The affine test soundness obstruction](research/artifacts/unique-games-affine-test-soundness-2026-09-07.md)
gives explicit 2-to-1 games of value at most `2/sqrt(N)` whose folded
long-code test outputs have high value. The proof, dependencies, and
[exact finite checks](scripts/check_unique_games_affine_soundness.py) are
integrated with Cairn and the Unique Games replay workflow. This rules out
that test's uniform soundness under only affine richness; it does not prove
or disprove UGC. Reproduce with
`python3 scripts/check_unique_games_affine_soundness.py --check`.

[A finite-ball limit on relation-energy proofs](notes/PROPERTY_T_FREE_FINITE_BALL_LIMIT_2026-09-07.md)
gives an elementary obstruction to controlling a nontrivial word by relation
errors on individual vectors, with linked research claims and proofs. It also
records the unresolved global operator-norm step in the independent search for
a property-(T)-free non-MF proof. This note supplies no new existence theorem
or Lean verification claim.

The [scalar-sensitive HS gap reduction](research/artifacts/hs-word-gap-linearization-2026-09-07.md)
and [finite word-certificate criterion](research/artifacts/hyperlinear-word-certificate-2026-09-07.md)
sharpen the nonhyperlinear research route in Cairn. The exact amplifier
replay is `python3 experiments/hs_word_gap_amplification_check.py`.
The group-specific matrix bound and nonhyperlinear existence remain open;
these research proofs carry no new Lean verification claim.

[Exact rational word-certificate checks](research/artifacts/hs-word-certificate-rational-search.md)
now provide replayable counterexamples to proposed HS energy coefficients.
The [Higman calculation](research/artifacts/higman-hs-word-coefficient-lower-bound.md)
forces its marked-word coefficient above `9/5` using explicit rational
2-by-2 unitaries. The [three-dimensional continuation](research/artifacts/higman-qutrit-coefficient-bound.md)
now refutes even coefficient `16` with exact rational matrices, including
the proposed coefficient `2` missed by the earlier bounded search.
Nonhyperlinear existence remains open. Replay the earlier witness with
`python3 experiments/hs_word_certificate.py verify research/artifacts/higman-hs-word-coefficient-witness.json`.
Replay the stronger witness with `python3 experiments/higman_qutrit_witness.py`.

The [complete two-dimensional bound](research/artifacts/higman-u2-bound.md)
proves coefficient `2` for every U(2) tuple using 56 exact Bernstein
certificate cells. Hence dimension `3` is minimal for its failure.
Run `python3 experiments/higman_u2_certificate.py verify`.
The Hyperlinear word research replay workflow checks both certificates,
the scalar-sensitive amplifier, and their Cairn dependencies on pushes.

[Exact rounder obstructions for quantum PCP](research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md)
gives a rational qubit-projector family with combinatorial gap `1/2` and
unbounded optimal rounder cost, plus an obstruction to flags charged only
to individual terms. Run `python3 scripts/check_qpcp_rounding.py` for exact
algebraic replay. The linked Cairn target remains open; these results do not
prove quantum PCP.

[Finite-context relator energy](research/artifacts/finite-context-relator-energy.md)
extends that obstruction to arbitrary fixed polynomial contexts and proves
that the resulting quadratic certificates characterize ordinary identity
words. Its [continuation](research/artifacts/local-context-and-global-norm-hierarchies.md)
computes the limit of increasing vector-context tests as the full group
C-star norm, and distinguishes it from the global norm test for the MF
radical. Complete written proofs and exact finite certificate replays are
included; these results do not settle the non-MF research goals.

[Gottschalk surjunctivity research](notes/GOTTSCHALK_RESEARCH_2026-09-07.md)
includes full written proofs of a conditional observable-growth criterion,
[generic Cantor fibers for local decoders](research/artifacts/gottschalk-decoder-fibers-2026-09-07.md),
and [sharp quantum compression obstructions](research/artifacts/gottschalk-quantum-compression-2026-09-07.md).
The fiber and matrix-extension criteria each have an explicit unresolved premise.
The [positive conjecture goal](research/gottschalk-surjunctivity-conjecture.md)
remains open in Cairn. Replay the accompanying exact checks with:

```sh
python3 research/artifacts/check-gottschalk-observable-growth-2026-09-07.py
python3 research/artifacts/check-gottschalk-decoder-fibers-2026-09-07.py
python3 research/artifacts/check-gottschalk-quantum-compression-2026-09-07.py
bin/cairn why gottschalk-surjunctivity-conjecture
```

[Fixed-list relation-energy certificates](notes/PROPERTY_T_FREE_CONTEXT_ENERGY_2026-09-07.md)
are characterized exactly by subgroup membership in a free group. The note
gives a linear bound on finite permutation counterexamples and an
[exact certificate generator and verifier](experiments/word_energy_certificate.py).
This is a proved limitation of the proposed certificate method; that method
does not supply a property-(T)-free non-MF existence theorem.

## Lean library

The Lean code is organized as a reusable library. Generic definitions and theorems are separated from concrete presentations and finite certificates, so other projects can import only the layers they need. [`GroupApproximation.lean`](GroupApproximation.lean) imports the complete library.

| Area | Directories | Contents |
| --- | --- | --- |
| Group theory | `Algebra/`, `GroupTheory/`, `Higman/`, `Covers/` | Presentations, normal forms, free products, HNN extensions, quotients, embeddings, and torsion |
| Finite approximation | `Sofic/`, `Criterion/`, `Stability/`, `Domination/`, `Matching/` | MF, sofic, and hyperlinear interfaces; finite models; residuals; matrix coronas; permanence and obstruction theorems |
| Rigidity | `PropertyT/`, `Kazhdan/`, `PropertyTT/` | Fixed-point methods, relative property (T), spectral and Hodge certificates, and property (TT)/T |
| Analysis | `Analysis/`, `KOne/`, `Leavitt/`, `Steinberg/` | Matrix estimates, projections, traces, C*-algebras, K-theory, and noncommutative rings |
| Other group constructions | `Kun/`, `KunThom/`, `Quantum/`, `Monsters/` | Graph, permutation, quantum, and embedding constructions |
| Public and checked interfaces | `Endpoint/`, `Meta/`, `Computability/`, `Manuscript/` | Stable exports, certificate replay, computability wrappers, statement matching, and axiom audits |

Modules named `Literal*` contain fully specified examples and certificate data; the generic modules do not depend on any particular presentation.

## Palomar submission

Version 1 of the explicit sofic non-MF theorem is registered as
[PALOMAR-2026-08-24-000006](https://palomar-registry.org/entry?id=PALOMAR-2026-08-24-000006&version=1).
The Mathlib-only statement is in `Palomar/Challenge.lean`, the proved copy is
in `Palomar/Solution.lean`, and `Palomar/comparator.json` records their
Comparator identity.
