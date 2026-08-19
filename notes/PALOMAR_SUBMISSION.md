# The Palomar submission

> Every prose section below is a TODO placeholder awaiting the author's own
> text.  What is filled in is factual and mechanical: file paths, the compared
> declaration name, and the checked prerequisites.

## The entry

Compared declaration: `ExplicitNonMF.explicit_fp_sofic_hyperlinear_not_MF`,
selected by `Palomar/comparator.json`.  One Comparator configuration is one
registry entry.

TODO: what the theorem says, clause by clause, in English.

## File map

| path | role |
|------|------|
| `Palomar/Challenge.lean` | the statement of record; imports Mathlib only |
| `Palomar/Solution.lean` | the same statement, proved from the development |
| `Palomar/comparator.json` | names the two modules and the compared theorem |
| `formalization.yaml` | registry metadata; `project.description` is the published abstract |
| `LICENSE` | Apache-2.0 at the repository root, matching `project.license` |
| `scripts/check_palomar_shared_block.py` | the gate on all of the above |

## Why the two files duplicate the definition block

TODO: prose.  The mechanical facts it has to explain: the challenge may import
Mathlib only; Comparator compares the exported statements syntactically and
then requires every constant they mention to be identical in both
environments, so the block cannot be shared by an import; the bridge to the
development is definitional and `ExplicitNonMF.E_eq` / `ExplicitNonMF.w_eq`
are the `rfl`s that pin it.

## Why the MF property is stated in the local operator-norm form

TODO: prose.  The mechanical fact it has to explain: Mathlib has no
C\*-algebra quotients, so the matrix corona cannot be named in a Mathlib-only
file; the two equivalences that license the local form are proved in this
repository as `manuscriptMFDefinitionEquivalences`, and the corona form of the
endpoint is `manuscriptTheoremA`.

## Mechanical prerequisites, as checked

| requirement | status |
|---|---|
| public GitHub repository | `SauersML/group-approximation`, public |
| exactly one root licence file, SPDX-detectable, matching `project.license` | `LICENSE`, Apache-2.0 |
| `lean-toolchain` naming a release at or above the registry minimum | `leanprover/lean4:v4.32.2` ≥ `v4.28.0` |
| exactly one of `lakefile.toml` / `lakefile.lean`, at most 1 MiB | `lakefile.toml` |
| committed `lake-manifest.json`; every Git package a public `https://github.com/…` URL at a full 40-character SHA | yes, 9 packages |
| no Git submodules, no LFS pointers | none |
| no committed compiled artifacts outside `.lake` | none |
| checkout at most 500 MiB excluding `.git` | about 56 MB tracked |
| challenge at most 100 KiB and 1000 lines | 319 lines |
| `permitted_axioms` exactly the three classical axioms, and the proof's closure matching | yes; `#audit_axioms` reports `[propext, Classical.choice, Quot.sound]` |
| `formalization.yaml` accepted by `PalomarSubmission/scripts/submission_contract.py` | yes; derived `result_origin: original`, `repository_role: substantive-development` |

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
is permanent publication.

## Not in this entry

One submission is one Comparator configuration, so these are separate entries:

1. TODO: the reduced group C\*-algebra statement.
2. TODO: the trace statement.
3. TODO: the undecidability statement, and Novikov–Boone.

TODO: prose on why each needs its own Challenge scaffolding.
