# A surjunctive group that is not sofic

This submission proves in Lean that **there exists a finitely generated
surjunctive group that is not sofic**. It answers the converse to the
Gromov-Weiss surjunctivity theorem, recorded as OP-11 in
[Ceccherini-Silberstein and Coornaert, *Cellular Automata and Groups*](https://doi.org/10.1007/978-3-642-14034-1)
and as Problem 1.1 in
[Bowen and Chapman](https://arxiv.org/html/2511.06586v1).

A group is surjunctive if every injective cellular automaton on its full
shift over a finite alphabet is surjective. A group is sofic if its finite
multiplication patterns have asymptotically faithful finite permutation
models in normalized Hamming distance. The challenge gives both definitions
explicitly and states the result with no additional hypotheses.

## The witness and the new argument

The witness is the symmetric double `G *_Γ G`, where

```text
Γ = EL₃(𝔽₂[x₁,x₂,x₃]),
G = EL₃(𝔽₂[x₁^±¹,x₂^±¹,x₃^±¹]) ⋊ EL₃(ℤ).
```

The action is monomial substitution. **Kun and Thom constructed this pair
and proved the double nonsofic**, in
[Theorems A and E](https://arxiv.org/html/2608.06222v3).
The new ingredient here is the theorem that a symmetric double of a
surjunctive group is surjunctive over any subgroup. Since `G` is residually
finite, this makes their double surjunctive. Its two vertex groups supply a
finite generating set.

The formal development proves both halves, including the permutation
centralizer normalization needed for Kun-Thom nonsoficity. The endpoint is
[`GroupApproximation.BowenChapman.exists_fg_surjunctive_not_isSofic`](GroupApproximation/BowenChapman/Endpoint.lean).
The original surjunctivity argument is recorded in the
[September 11 proof](research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md).
The sources and the statement comparison are detailed in
[`formalization.yaml`](formalization.yaml).

Bowen and Chapman's theorem concerns invariant random subgroups and leaves
the group question open. This submission proves the group statement. It
asserts finite generation; finite presentation is not part of the selected
formal result.

## Submission files

| Item | Path |
| --- | --- |
| Comparator configuration | [`Palomar/comparator-bowen-chapman.json`](Palomar/comparator-bowen-chapman.json) |
| Auditable statement | [`Palomar/BowenChapmanChallenge.lean`](Palomar/BowenChapmanChallenge.lean) |
| Proof | [`Palomar/BowenChapmanSolution.lean`](Palomar/BowenChapmanSolution.lean) |
| Metadata and credits | [`formalization.yaml`](formalization.yaml) |

The configuration selects exactly:

- `BowenChapman.not_all_surjunctive_groups_sofic`
- `BowenChapman.exists_finitelyGenerated_surjunctive_not_sofic`

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The challenge's `sorry` declarations are the statements Comparator must
match; they are not imported by the solution.

The `Palomar Comparator` workflow runs the selected configuration through
Lean's kernel and, when dispatched with `nanoda=true`, NanoDa. The
`Palomar check` workflow checks metadata, statement agreement, and axiom
closures. Use the runs for the exact submitted commit.

## Credit

Astra developed the original surjunctivity argument using a custom proof
tool under the author's direction. Claude (Anthropic) produced the Lean
development and original exposition. Codex (OpenAI) prepared this submission's
README and metadata and audited the package. The human author is responsible
for the submission. The mathematical sources are credited separately in
`formalization.yaml`. The repository is released under [Apache-2.0](LICENSE).
