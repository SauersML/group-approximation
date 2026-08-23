---
rg: 2
id: sequential-character-recentering-has-decision-tree-loss
kind: claim
title: Sequential two-character recentering has an unavoidable character decision-tree loss
distinct_from:
  sequential-pinchings-have-sharp-linear-disturbance-loss: that uses a sparse Clifford cycle and coordinate measurement disturbance; this is the elementary information lower bound even for an exact scalar code-character menu
  two-code-character-cut-recenters-to-one-coordinate: that proves one recentered cut is cheap; this shows why summing that estimate one binary split at a time is not dimension-free
---

Let `D` be a finite set of distinct binary code characters and consider a
binary decision tree whose internal nodes query one coordinate sign and
whose leaves identify every character in `D`.  Under the uniform
distribution on `D`, its average depth is at least

```text
log_2 |D|.                                                (SCR1)
```

Therefore a proof which constructs the global character PVM solely by
repeatedly applying `two-code-character-cut-recenters-to-one-coordinate`
and pays the same complete-pair row upper bound at every visited node can
lose a factor at least `log |D|`.  Since a positive-rate code has
exponentially many characters, this loss is not dimension- or
length-independent.

This does not refute global PVM alignment.  It proves that the two-leaf CS
lemma must be aggregated simultaneously--for example by a multiway
complete-pair minor, a gauge-covariant square function, or a direct joint
PVM construction--rather than summed along a character-query tree.

Nor does it refute weighted random hashing.
`weighted-code-character-hash` shows
that `O(log(1/eta))` nonadaptive coordinates leave only an `eta` fraction of
arbitrarily weighted distinct-character boundary, independently of the
number of represented characters.  The entropy lower bound applies only to
exact identification of every leaf.

## Attempts

Choosing a balanced coordinate at every node attains logarithmic depth but
does not remove it.  Highly unbalanced choices only increase average depth.
Code distance ensures every pair has many possible separating coordinates;
it does not reduce the information needed to identify one of `|D|`
characters when the proof charges each binary query separately.
