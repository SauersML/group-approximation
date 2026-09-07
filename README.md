# Group Approximation

The remote `verified` branch is automatically fast-forwarded after every complete Lean Prover CI success on `main`. Use that for the most recent correct Lean code.

## A non-MF group

[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every group is MF. [`non_mf_group_notes.tex`](non_mf_group_notes.tex) is an archived research notebook for an earlier construction and is not a companion to the current manuscript.

[`non_mf_groups_exist.pdf`](non_mf_groups_exist.pdf) at the repository root is the distribution PDF, rebuilt from the root TeX source by the draft PDF workflow. The obsolete duplicate under `output/pdf/` has been removed. A draft PDF build does not certify the manuscript's Lean coverage.

## Research notes

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

[Exact rounder obstructions for quantum PCP](research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md)
gives a rational qubit-projector family with combinatorial gap `1/2` and
unbounded optimal rounder cost, plus an obstruction to flags charged only
to individual terms. Run `python3 scripts/check_qpcp_rounding.py` for exact
algebraic replay. The linked Cairn target remains open; these results do not
prove quantum PCP.

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
