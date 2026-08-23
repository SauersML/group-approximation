---
rg: 2
id: terminal-common-pinching-displacement-vanishes
kind: claim
title: The terminal gap decomposition has vanishing common pinching displacement
distinct_from:
  balanced-parity-multicut-boundary-is-summable: that bundled cut-tree boundary, repeated parity repair, spike trace, and terminal gaps; exact cut Pythagoras and adaptive spike budgeting reduce it to this one displacement assertion
  hs-one-level-expander-block-decomposition: that concerns arbitrary almost representations; this may use exact balanced parity, its Loewner fundamental-cone inequalities, and complete-pair energy
---

OPEN.  In the setting of
`balanced-parity-multicut-boundary-is-summable`, after assigning spike
quarantines a prescribed vanishing total trace, construct a nested terminal
PVM `(f_a)` such that, after taking the polar signs of the terminal
contractions `f_aQ_if_a`, every retained terminal reflection tuple has
generated-adjoint gap at least `lambda_0`, where

```text
lambda_0->0,                 epsilon/lambda_0->0,
```

and

```text
(1/L)sum_i||Q_i-sum_a f_aQ_if_a||_2^2=o(1).             (TCP1)
```

By `nested-common-cuts-have-exact-pythagorean-boundary-ledger`, `(TCP1)` is
exactly the total boundary of the full cut tree.  Thus no separate entropy,
tree-depth, or repeated-boundary estimate remains.  By deferring sign until
this terminal PVM is obtained, the common compression/sign ledger charges
all parity and complete-pair damage once at the same `o(1)` cost.

The remaining content is a parity-aware expander decomposition in the
strong metric `(TCP1)`.  The Loewner parity inequality controls the
coordinate distribution of each individual cut boundary but does not yet
bound the final pinching displacement.

The exact two-leaf gauge problem is now solved by
`two-code-character-cut-recenters-to-one-coordinate`: a coordinate on which
the two terminal characters differ supplies a spectral cut whose complete
boundary is one commutator row, hence `O(E_com)`.  The remaining obstruction
is genuinely multi-character.  Sequentially applying that lemma incurs the
`log |D|` character decision-tree loss proved in
`sequential-character-recentering-has-decision-tree-loss`.  The sharp final
gate is therefore `multicharacter-pvm-alignment-modulo-simultaneous-gauge`,
which asks for simultaneous rather than sequential CS alignment.

## Attempts

1. **Entropy charging.**  Unnecessary but also insufficient: it introduces
   dimension-dependent depth.  Exact cut Pythagoras removes duplicate
   charges, but only gives the coarse upper bound one rather than `o(1)`.
2. **Central mixtures of sparse Clifford cycles.**  These red-team a generic
   expander decomposition, but not `(TCP1)` under exact positive-distance
   parity.  Central summand cuts have zero boundary, and
   `central-clifford-parity-sectors-round-uniformly` rounds every remaining
   scalar-commutator sector.  A counterexample here must have genuinely
   noncentral spectral commutators.
3. **Repeated intermediate signs.**  They can recycle boundary and invalidate
   Pythagoras.  `low-gap-cut-and-spike-dichotomy-holds-for-contractions`
   proves that coarea and clipping can instead run directly on every
   compressed contraction tuple.  Thus a contraction tree followed by one
   terminal sign is certified; the only remaining issue is `(TCP1)` itself.
