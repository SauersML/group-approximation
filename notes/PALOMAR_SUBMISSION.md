# The Palomar submission

[Palomar](https://palomar-registry.org) is a registry of machine-checked Lean
proofs, incubated by the Lean FRO and ICARM and opened for submissions on
2026-08-18.  It records an exact commit of a public GitHub repository together
with a small set of Lean declarations that state a result.  A submission
passes two gates: mechanical verification by
[Comparator](https://github.com/leanprover/comparator) plus a replay through
Lean's kernel and the independent NanoDa kernel, and an automated editorial
review that reads the informal account against the Lean.  It is not peer
review and it is not a journal.

This document is the record of what this repository submits, why it is shaped
the way it is, and how to submit it again.

## The entry

Compared declaration: `ExplicitNonMF.explicit_fp_sofic_hyperlinear_not_MF`,
selected by `Palomar/comparator.json`.  One Comparator configuration is one
registry entry.

For the explicit eight-generator, forty-one-relator group `E` and its
distinguished word `w = [tct⁻¹, v₁(tct⁻¹)v₁⁻¹]`, the theorem states:

| # | clause | what it says |
|---|--------|--------------|
| 1 | `Group.IsFinitelyPresented E` | `E` is finitely presented — cheap, since it is *defined* by a finite presentation |
| 2 | `w ≠ 1 ∧ w² = 1 ∧ ∀ g, Commute w g` | `w` is a nontrivial central involution; the load-bearing clause, without which 6–10 are vacuous |
| 3 | `∃ S : Finset E, S.card ≤ 6 ∧ closure S = ⊤` | six elements generate `E` |
| 4 | `IsSoficGroup E` | permutation models in normalized Hamming distance |
| 5 | `IsHyperlinearGroup E` | unitary models in normalized Hilbert–Schmidt distance |
| 6 | asymptotic-representation clause | every operator-norm asymptotic unitary representation sends `w` to `1` |
| 7 | uniform clause | one defect budget, one finite test set, every dimension: `‖φ w − 1‖ < 1` |
| 8 | `¬ IsMFGroup E` | no operator-norm models separate the elements of `E` |
| 9 | finite-dimensional clause | every finite-dimensional representation over every field sends `w` to `1` |
| 10 | finite-quotient clause | so does every homomorphism to a finite group |

Clauses 4, 5 and 8 are the point: the same group, the same finite-dimensional
models, three metrics, and the answer flips exactly when the metric becomes
the operator norm.

Axiom closure, gated inside the build by `#audit_axioms`:
`[propext, Classical.choice, Quot.sound]` — exactly the three the registry
permits.

## File map

| path | role |
|------|------|
| `Palomar/Challenge.lean` | the statement of record; imports Mathlib only |
| `Palomar/Solution.lean` | the same statement, proved from the development |
| `Palomar/comparator.json` | names the two modules and the compared theorem |
| `formalization.yaml` | registry metadata; `project.description` is the published abstract |
| `LICENSE` | Apache-2.0 at the repository root, matching `project.license` |
| `scripts/check_palomar_submission.py` | the source-level gate on all of the above (self-calibrating) |
| `scripts/check_palomar_statement_match.sh` | compares the compared statement as ELABORATED in the two modules |
| `scripts/Palomar{Challenge,Solution}Type.lean` | the two drivers that dump it |

## Why the two files duplicate the definition block

The Challenge may import nothing but Mathlib: the registry recompiles it
against a frozen canonical Mathlib and rejects any project-local source in its
transitive import closure.  So everything the statement mentions — the
alphabet, the forty-one relators, `E`, `w`, and the three approximation
notions — is spelled out there in Mathlib terms.

The Solution cannot then *import* those definitions, because Comparator
compares the two exported statements **syntactically** and afterwards walks
every constant the statement mentions, requiring each to be identical in both
environments (`Comparator/Compare.lean`).  A constant that exists in only one
of them is a mismatch, not a match.  So the block is copied byte for byte, and
`scripts/check_palomar_submission.py` fails the build if the two copies ever
differ.

Text comparison cannot see a difference that appears only after elaboration —
a different instance resolved on one side, a coercion inserted on one side.
`scripts/check_palomar_statement_match.sh` covers that: it dumps the compared
declaration's level parameters, structural type hash, sorted used-constant
list and `pp.all` type from each module's own environment and diffs them.  On
this tree both sides give type hash `2455476343` over 110 used constants.

The bridge from the copy to the development is definitional, not
propositional: the copied definitions elaborate to the same terms as
`GroupApproximation.LiteralNonMFPresentation.relators`, `…MarkedGroup` and
`…mark`.  `ExplicitNonMF.E_eq` and `ExplicitNonMF.w_eq` in the Solution are
two `rfl`s that pin this down and stop compiling the moment it stops being
true.

## Why MF is stated in the local form

The Carrión–Dadarlat–Eckhardt definition quantifies over homomorphisms into
the unitary group of `∏ₙ M_{dₙ}(ℂ) / ⊕ₙ M_{dₙ}(ℂ)`.  Mathlib has no
C\*-algebra quotients and no group C\*-algebras, so that object cannot be
named in a Mathlib-only file without building it there first.

It does not need to be.  The unitary group of the quotient is canonically
isomorphic to `∏ₙ 𝒰(dₙ)` modulo the sequences converging to `1` in operator
norm, so a homomorphism into it is exactly an operator-norm asymptotic unitary
representation (clause 6); and the resulting property is equivalent to the
local form with separation constant `1` (clause 8), by tensor-power
amplification.  Both equivalences are proved in this repository —
`isCDEOperatorMF_iff_isOperatorMF` and
`isOperatorMF_iff_isNormApproximable_one`, packaged as
`ManuscriptExactWrappers.manuscriptMFDefinitionEquivalences` — and the
embedding form of the endpoint itself is
`LiteralNonMFEndpoint.manuscriptTheoremA`.  `formalization.yaml` records this
under `fidelity.divergences`, and the Challenge's module documentation says it
where a reader of the statement will see it.

## What the registry's own record says to expect

Of the thirteen entries registered as of 2026-08-19, all reached outcome
`neutral` and all carry trust level `high`.  Three carry a published warning,
and they map onto the three risks this submission is shaped around:

- `elliotglazer/erdos501` — declaration-specific prose advertised a stronger
  conclusion than the compared theorem states.  Hence the explicit paragraph,
  in both the abstract and the Challenge documentation, naming the C\*-algebra,
  trace, quotient and undecidability results as **not** part of this
  configuration.
- `teorth/sendov` — narrow novelty claims unsupported by a documented
  literature search.  Hence the dated search recorded in the `original-proof`
  source note, with what it covered and what it found, and the explicit
  statement that the novelty of the formalization is unknown.
- `rkirov/jordan_pick` — an MSC code materially unrelated to the result.
  Hence the classification trimmed to the four codes the selected theorem
  actually touches; the decision-problem code was dropped along with the
  undecidability corollary.

Challenge size is not a concern: `WillWhistler/Regts-Sevenster` registered at
999 lines and 40,610 bytes with trust `high`, carrying only the
`Challenge exceeds the preferred audit surface` note.  This challenge is 532
lines and 25,669 bytes, so it trips the line threshold and not the byte one.
Deleting docstrings to clear it would trade a note in the report for a risk on
the definition-fidelity check, which is mandatory and scored.

## Mechanical prerequisites, as checked

| requirement | status |
|---|---|
| public GitHub repository | `SauersML/group-approximation`, public |
| exactly one root licence file, SPDX-detectable, matching `project.license` | `LICENSE`, Apache-2.0 |
| `lean-toolchain` naming a release at or above the registry minimum | `leanprover/lean4:v4.32.2` ≥ `v4.28.0` |
| exactly one of `lakefile.toml` / `lakefile.lean`, at most 1 MiB | `lakefile.toml` |
| committed `lake-manifest.json`; every Git package a public `https://github.com/…` URL at a full 40-character SHA | yes, 9 packages |
| no Git submodules, no LFS | none |
| no committed compiled artifacts outside `.lake` | none |
| checkout at most 500 MiB excluding `.git` | about 56 MB tracked |
| challenge at most 100 KiB and 1000 lines | 532 lines / 25,669 bytes |
| `permitted_axioms` exactly the three classical axioms, and the proof's closure matching | yes; `#audit_axioms` reports `[propext, Classical.choice, Quot.sound]` |
| `formalization.yaml` accepted by `PalomarSubmission/scripts/submission_contract.py` | yes; derived `result_origin: original`, `repository_role: substantive-development` |
| challenge and solution elaborate the same statement | yes; type hash `2455476343`, 110 used constants |

## How to submit

Submissions go only through <https://submit.palomar-registry.org>.  The form
asks for:

- the repository, as `owner/name`: `SauersML/group-approximation`;
- the full 40-character commit SHA (branches and tags are not accepted);
- the repository-relative Comparator configuration path:
  `Palomar/comparator.json`;
- the submitter's relationship to the substantive formalization: either
  "responsible author or maintainer" or "approval from one".  This is a claim
  about a person and is recorded permanently.

Write access is proved separately, by browser sign-in or, for an agent with no
browser, by a tag at the submitted commit together with a gist.  The submitter
sees the editorial review before deciding whether to register it; registration
is permanent publication, and it forks the repository and every pinned
dependency into `PalomarArchive` with immutable preservation tags.

## Not in this entry

One submission is one Comparator configuration, so these are separate entries:

1. **Theorem C** — `C*ᵣ(E)` is separable, has a faithful tracial state, is
   therefore stably finite, and is not MF: an explicit stably finite separable
   non-MF C\*-algebra, which Blackadar–Kirchberg recorded as unknown.
2. **Theorem E** — the canonical trace on `C*ₘₐₓ(E)` is hyperlinear but not
   MF, answering Shulman's question negatively.
3. **Undecidability** — no algorithm decides MF-ness from a finite
   presentation; and Novikov–Boone, whose statement is already Mathlib-only at
   zero cost.

(1) and (2) each need the reduced or maximal group C\*-algebra, the MF-algebra
notion, and the hyperlinear/MF trace notions constructed inside their own
Challenge from `ℓ²(E)` and bounded operators, because Mathlib has none of
them.  That is a formalization lane, not packaging, and it should follow a
clean first review rather than gate it.
