---
rg: 2
id: binary-leavitt-level-synchronous-first-mismatch-area-cell
kind: claim
title: Pay equal-level Morita first mismatches by one bounded Steinberg cell
refuted_by: level-synchronous-first-mismatch-area-is-centralizer-impossible
distinct_from:
  binary-leavitt-first-mismatch-morita-area-cell: that quantifies over arbitrary unrelated tails and is refuted by freezing one tail in an infinite centralizer section; this asks only for equal-length tails, exactly as produced by equal-depth complete-graph vertices.
  atlas-steinberg-context-absorption: that proves qualitative context vanishing; this asks for a uniform area comparison for the original cross-branch commutator on the level-synchronous family.
---

**REFUTED.**  In the notation of `(MTR1)--(MTR2)`, no constant `A_sync`
satisfies

```text
Area([c_(ia),h_(jb)])<=A_sync                             (LSM1)
```

for both `i!=j` and every pair of binary tails with `|a|=|b|`.

At a fixed level `n`, freeze one tail `b` and vary all `2^n` tails `a`.
Conjugating `h_(jb)` back to the base involution preserves every commutator
area and turns the `c_(ia)` into `2^n` distinct centralizer cosets of that one
fixed involution.  The bounded-area part of its centralizer has only finitely
many cosets by `finite-mark-centralizer-commutator-area-is-proper`, giving a
contradiction for large `n`.  The full proof is
`level-synchronous-first-mismatch-area-is-centralizer-impossible`.

The exact coefficient remains one defining zero relation with contexts,

```text
r_a(t_i s_j)s_b=0.                                      (LSM2)
```

and context absorption supplies a constant-area nested null word.  The
refutation proves that comparison from the original cross-branch word to the
nested word must have unbounded area on the synchronous family.

## Attempts

* **Asynchronous strengthening.**  Allowing arbitrary tail lengths is false:
  `unsynchronized-first-mismatch-area-is-centralizer-impossible` freezes one
  tail and invokes properness of commutator area in the resulting infinite
  centralizer section.  Equal levels evade that obstruction but still need a
  new simultaneous two-tail diagram.
* **Qualitative spare-index transfer.**  Exact split independence identifies
  `(LSM1)` with the nested context word.  Its existing induction spends one
  shorter commutation filling per level, so it gives no uniform bound.  A
  successful diagram must cancel the two synchronized transfer ladders
  against each other before paying their cells.
* **Freeze one column at each level.**  Conjugate the frozen `h_(jb)` to the
  fixed base `h`.  The entire level becomes an exponentially large section
  of `C_G(h)/<h>` with the same proposed area bound.  Properness of
  finite-mark centralizer area refutes that bound.
