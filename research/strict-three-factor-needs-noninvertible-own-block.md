---
rg: 2
id: strict-three-factor-needs-noninvertible-own-block
kind: claim
title: A strict three-factor automaton must, in every ordering, expose a row whose own-block map is not a local bijection
distinct_from:
  controlled-self-linear-feedback-ca-are-surjunctive: that gives a surjunctivity conclusion when every own part is a bijective linear automaton; this is the contrapositive-shaped structural statement that a strict automaton must fail own-block local bijectivity somewhere in every ordering, and it locates the failure at the B1 and B3 direct-finiteness boundaries.
  three-factor-finite-alphabet-ca-are-surjunctive: that is the open normal-form restatement of the whole conjecture; this is a proved structural constraint on any counterexample within that normal form, not a decision of it.
artifacts:
  - research/artifacts/corrected-tail-peeling-boundary-2026-09-12.md
---

Let `F` be an injective three-factor cellular automaton that is strict (not
surjective). Then in every ordering of every block presentation, the peeling
chain (type (Z), type (O), own-block local-bijection steps) halts before the
empty tail at a row whose own-block self-map `Phi_Y` is not a local bijection.

The failure is one of exactly two kinds, each already an open direct-finiteness
question:

- **(B1)** the row is own-linear but some `L_Y` is not bijective, which contains
  stable finiteness of `R[G]`;
- **(B3)** the own-block map is nonlinear and not a local bijection, whose
  minimal case is `central-c3-quadratic-surjunctivity-iff-direct-finiteness`,
  equivalent to characteristic-two direct finiteness.

So strictness in the three-factor normal form lives precisely at own-block maps
that are not local bijections. For counterexample design this means any candidate
whose every row is an own-block local bijection under some ordering is surjective
and can be discarded, and a live design must carry a genuinely non-invertible
own-block row over a non-surjunctive memory group.

## Attempts

Proved in Section 3 (Theorem 3.1) of the artifact. If some ordering peeled every
block by type (Z)/(O)/local-bijection steps, `F` would be fully peelable, hence
surjective (`peeling-to-surjunctive-memory-tail-forces-surjectivity` with the
empty, trivial-subgroup tail), contradicting strictness. So every ordering has a
non-peelable row, i.e. an own-block self-map that is not a local bijection; the
B1 and B3 dichotomy is the classification of that failure. Established by the
companion route. Open extension: whether B1 or B3 can actually occur over a
nonsofic host is the counterexample question itself.
