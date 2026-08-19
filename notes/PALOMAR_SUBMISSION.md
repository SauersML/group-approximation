# The Palomar submission

[Palomar](https://palomar-registry.org) is a registry of machine-checked Lean
proofs, incubated by the Lean FRO and ICARM and opened for submissions on
2026-08-18.  It records an exact commit of a public GitHub repository together
with a small set of Lean declarations that state a result.  A submission
passes two gates: mechanical verification by
[`leanprover/comparator`](https://github.com/leanprover/comparator) plus a
kernel replay through NanoDa, and an automated editorial review that reads the
informal account against the Lean.  It is not peer review and it is not a
journal.

This document is the record of what this repository submits, why it is shaped
the way it is, and how to submit it again.

## The entry

**`ExplicitNonMF.explicit_fp_sofic_hyperlinear_not_MF`** — one theorem, one
Comparator configuration, one registry entry.  It states, about the explicit
eight-generator forty-one-relator group `E` and its distinguished word
`w = [tct⁻¹, v₁(tct⁻¹)v₁⁻¹]`:

| # | clause | what it says |
|---|--------|--------------|
| 1 | `Group.IsFinitelyPresented E` | `E` is finitely presented (cheap: it is *defined* by a finite presentation) |
| 2 | `w ≠ 1 ∧ w² = 1 ∧ ∀ g, Commute w g` | `w` is a nontrivial central involution — the load-bearing clause, without which the rest is vacuous |
| 3 | `IsSoficGroup E` | permutation models in normalized Hamming distance |
| 4 | `IsHyperlinearGroup E` | unitary models in normalized Hilbert–Schmidt distance |
| 5 | asymptotic-representation clause | every operator-norm asymptotic unitary representation sends `w` to `1` |
| 6 | `¬ IsMFGroup E` | no operator-norm models separate the elements of `E` |
| 7 | finite-dimensional clause | every finite-dimensional representation over every field sends `w` to `1` |

Clauses 3, 4 and 6 are the point: the same group, the same finite-dimensional
models, three metrics, and the answer flips exactly when the metric becomes
the operator norm.  So soficity and hyperlinearity do not imply the MF
property, and the MF conjecture is false with an explicit witness.  Clause 7
adds that `E` is not residually finite-dimensional, not LEF and not residually
finite.

Axiom closure, gated inside the build by `#audit_axioms`:
`[propext, Classical.choice, Quot.sound]` — exactly the three the registry
permits.

## File map

| path | role |
|------|------|
| `Palomar/Challenge.lean` | the statement of record.  Imports **Mathlib only** |
| `Palomar/Solution.lean` | the same statement, proved from the development |
| `Palomar/comparator.json` | names the two modules and the compared theorem |
| `formalization.yaml` | the registry metadata; `project.description` is the published abstract |
| `LICENSE` | Apache-2.0 at the repository root, matching `project.license` |
| `scripts/check_palomar_shared_block.py` | the gate on all of the above |

## Why the two files duplicate 250 lines

The Challenge may import nothing but Mathlib: the registry recompiles it
against a frozen canonical Mathlib and rejects any project-local source in its
transitive import closure.  So everything the statement mentions — the
alphabet, the forty-one relators, `E`, `w`, and the three approximation
notions — is spelled out there in Mathlib terms.

The Solution cannot then *import* those definitions, because Comparator
compares the two exported statements **syntactically** and afterwards walks
every constant the statement mentions, requiring each to be identical in both
environments (`Comparator/Compare.lean`).  A constant that exists in only one
of them is a mismatch, not a match.  So the block is copied, byte for byte,
and `scripts/check_palomar_shared_block.py` fails the build if the two copies
ever differ.

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
representation (clause 5); and the resulting property is equivalent to the
local form with separation constant `1` (clause 6).  Both equivalences are
proved in this repository — `isCDEOperatorMF_iff_isOperatorMF` and
`isOperatorMF_iff_isNormApproximable_one`, packaged as
`ManuscriptExactWrappers.manuscriptMFDefinitionEquivalences` — and the corona
form of the endpoint itself is `LiteralNonMFEndpoint.manuscriptTheoremA`.
`formalization.yaml` records this under `fidelity.divergences`, and the
Challenge's module documentation says it where a reader of the statement will
see it.

## Mechanical prerequisites, as checked

| requirement | status |
|---|---|
| public GitHub repository | `SauersML/group-approximation`, public |
| exactly one root licence file, SPDX-detectable, matching `project.license` | `LICENSE`, Apache-2.0; GitHub's detector agrees |
| `lean-toolchain` naming a release ≥ the registry minimum | `leanprover/lean4:v4.32.2` ≥ `v4.28.0` |
| exactly one of `lakefile.toml` / `lakefile.lean`, ≤ 1 MiB | `lakefile.toml` |
| committed `lake-manifest.json`, every Git package a public `https://github.com/…` URL at a full 40-char SHA | yes, 9 packages |
| no Git submodules, no LFS pointers | none |
| no committed compiled artifacts outside `.lake` | none |
| checkout ≤ 500 MiB excluding `.git` | ~56 MB tracked |
| Challenge ≤ 100 KiB and ≤ 1000 lines | ~430 lines (over 300, so it draws the registry's "harder to audit" advisory — accepted, because the presentation is the point of the entry) |
| `permitted_axioms` exactly the three classical axioms | yes, and the proof's closure matches |
| `formalization.yaml` accepted by `PalomarSubmission/scripts/submission_contract.py` | yes; derived `result_origin: original`, `repository_role: substantive-development` |

## How to submit

Submissions go only through <https://submit.palomar-registry.org>; an agent
acting on someone's behalf should read `llms.txt` there first.  The form asks
for:

- the repository, as `owner/name`: `SauersML/group-approximation`;
- the **full 40-character commit SHA** — branches and tags are not accepted;
- the repository-relative Comparator configuration path:
  `Palomar/comparator.json`;
- the submitter's relationship to the substantive formalization.  The
  permitted answers are "responsible author or maintainer" or "approval from
  one".  Write access, organisation membership and forks are none of them.
  This is a claim about a person and is recorded permanently.

Write access is proved separately, by browser sign-in or, for an agent with no
browser, by a tag at the submitted commit together with a gist.

The submitter sees the editorial review first and then decides whether to
register it.  Registration is permanent publication: it publishes the redacted
review, forks the repository and every pinned dependency into
`PalomarArchive`, and creates immutable preservation tags.

## Deliberately not in this entry

One submission is one Comparator configuration, so the following are separate
entries to be prepared later, in this order:

1. **Theorem C** — `C*ᵣ(E)` is separable, has a faithful tracial state, is
   therefore stably finite, and is not MF: an explicit stably finite separable
   non-MF C\*-algebra, which Blackadar–Kirchberg recorded as unknown.
2. **Theorem E** — the canonical trace on `C*ₘₐₓ(E)` is hyperlinear but not
   MF, answering Shulman's question negatively.
3. **Undecidability** — no algorithm decides MF-ness from a finite
   presentation; and Novikov–Boone, whose statement is already Mathlib-only at
   zero cost.

(1) and (2) each need the reduced or maximal group C\*-algebra, the MF-algebra
notion, and the hyperlinear/MF trace notions constructed inside their
Challenge from `ℓ²(E)` and bounded operators, because Mathlib has none of
them.  That is a real formalization lane, not packaging, and it should follow
a clean first review rather than gate it.
