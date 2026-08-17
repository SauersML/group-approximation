---
rg: 2
id: adian-rabin-transform-for-mf
kind: claim
title: An effective Adian-Rabin transformation exists for the MF Markov property
distinct_from:
  operator-mf-is-a-markov-property: that is the Markov premise the construction consumes and is established; this is the construction itself, which is what remains open.
  torsion-free-higman-embedding: that is an embedding theorem for recursively presented groups; this is a computable map on finite presentations with a triviality-versus-containment dichotomy, and Higman embedding is one of the routes it must *avoid* needing.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Computability/MarkovMFConsequences.lean
  - GroupApproximation/Computability/AdianRabinMarkovProperty.lean
  - GroupApproximation/Computability/CStarRecognitionConsequences.lean
---

OPEN.  There is a finitely presented group with undecidable word problem and a
**computable** map taking an instance `(P, w)` of its word problem to a finite
presentation `P_w` such that

- `G(P_w)` is trivial — hence MF — when `w = 1`, and
- `E` embeds in `G(P_w)` — hence `G(P_w)` is not MF, by subgroup heredity —
  when `w != 1`,

together with the correctness equivalence in that form.  In Lean this is the
fourth field of `MarkovMFConsequences.AdianRabinReduction`: the computable
`transform` and its `correct` equivalence.  The other three fields are
inhabited (see [[operator-mf-is-a-markov-property]]), so this single datum is
the whole remaining input.

This is the manuscript's one declared literature input, used in exactly one
place: "This corollary carries one classical literature input, used only here:
the Adian--Rabin construction itself, which we have not formalized."

## The cost, itemized

`Computability/AdianRabinMarkovProperty` records the dependency chain and its
estimated size, because the honest thing to say about this hole is how big it
is rather than that it is "routine":

| | Obligation | Estimate |
|---|---|---|
| D1 | computable syntax of presentations (the coding layer) | done, see the Markov-property claim |
| D2 | the word problem of a finite presentation is r.e. — certificate search over conjugated relators | 300--600 lines |
| D3 | Markov--Post: undecidable word problem for finitely presented semigroups, by simulating a machine with a semi-Thue system | **done**, see below |
| D4 | Novikov--Boone: a finitely presented group with undecidable word problem, via an HNN tower | in progress, see below |
| D5 | the Adian--Rabin construction, effectively: Rabin's chain of HNN extensions and free products, with the collapse-to-trivial induction | 1500--3000 lines |
| D6 | assembly into `AdianRabinReduction` | 100--200 lines |

Mathlib's Britton's Lemma, HNN normal form and `PushoutI` are genuine enablers
and cut D4 and D5 substantially; D4 has to the best of current knowledge never
been done in any proof assistant.

**D3 is closed** (2026-08-16), unconditionally and with no literature input:
[[markov-post-undecidable-monoid-word-problem]].  It was not, however, on the
critical path.  The route taken to D4 is Aanderaa--Cohen modular machines
rather than Boone--Britton, and that route takes its computational input
directly from a machine, not from a monoid word problem — so
[[novikov-boone-fp-group-undecidable-word-problem]] neither uses D3 nor is made
cheaper by it.  The two are independent, and the earlier reading of D3 → D4 as
a critical path was wrong about the dependency, not merely about the order.

**D4 is under way**: six of its ten stages are proved, and the remaining
frontier is the good-subgroup lemma [[hnn-good-subgroup-lemma]] (the only step
with mathematical risk), finite presentability of the final group
[[boone-final-group-finitely-presented]], and the one deliberately unstated
external input [[modular-machine-with-noncomputable-halting]].

This claim now carries a decomposition rather than standing alone as a hole:
the route `adian-rabin-transform-via-boone-source-and-rabin-chain` reduces it to
D4 together with [[rabin-chain-effective-collapse-dichotomy]], which is D5 as a
claim in its own right — uniform in the forbidden group and with no
computability in it.  D6 is the route's own content.

## Four shortcuts that do not exist

Recorded so they are not re-attempted:

1. *Only this one Markov property is needed, not all of them.*  True, but
   Adian--Rabin is uniform in the forbidden group; specializing to this
   repository's `E` removes no step.
2. *Use the halting problem as the source instead of the word problem.*  The
   reduction must output group presentations and its correctness is stated in
   terms of a group element being trivial, so some finitely presented group
   with undecidable word problem is unavoidable — D4 cannot be dodged by
   changing the source.
3. *Exploit MF-specific structure.*  MF holds for all countable residually
   finite groups, so the positive side could target more than the trivial
   group; but Adian--Rabin already targets the trivial group, the strongest
   positive case, and the difficulty is the negative side plus the collapse
   dichotomy.
4. *Use a finitely generated recursively presented group with undecidable word
   problem.*  Elementary to build, but the decision problem is over **finite**
   presentations, and bridging the two is Higman embedding — strictly harder
   than D4.

The one genuinely separable piece is D2, worth roughly 5% of the total: it is
what upgrades "undecidable" to "not even recursively enumerable", and nothing
else depends on it.

## A second consumer

`Computability/CStarRecognitionConsequences` parameterizes the same reduction
over five group-C-star recognition predicates from the manuscript (MF-ness of
the reduced and maximal group C-star algebras, and finiteness, stable
finiteness and direct finiteness of the maximal one).  It postulates no
Adian--Rabin transformation, no construction of a group C-star algebra, and no
operator-algebra inheritance result: each of its undecidability theorems takes
the reductions as data.  So this claim gates that lane too, alongside the
group-C-star semantics those predicates would need.
