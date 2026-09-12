---
rg: 2
id: kl-four-same-sign-corner-words-inject
kind: claim
title: A nonsingular word with at least four same-sign corners injects unless two of them close a trivial star-graph 2-cycle
invalidates: [leavitt-kl-violation-from-distinct-same-sign-labels]
distinct_from:
  kl-unit-exponent-words-inject-when-same-sign-corners-are-free: that needs the same-sign labels to generate a free group of rank e-1 and no absorbed loop, which is the only available fence at two same-sign corners; this needs only that no two same-sign corners close a trivial 2-cycle, once there are at least four of them (three with two extra short-cycle conditions).
  kl-length-six-four-sign-change-words-inject: that settles the two length-six classes with two same-sign corners; this settles the remaining classes +++++- and ++++--, which have four.
  leavitt-paired-quotient-passes-relative-weight-test: that proves injectivity for the paired quotient of one specific Leavitt candidate from its specific labels; this proves injectivity for every word with four pairwise distinct same-sign labels over every group, and covers that candidate directly.
  kl-small-cancellation-words-inject-every-coefficient-group: that fences by exact syllable repetition from ten variable occurrences on; this fences by the labels of the star graph at every length.
---

Let `G` be any group and let `w in G * <t>` be cyclically reduced, not a
proper power, with `deg_t(w) = m != 0`. Split every power `t^(+-k)` into
single letters, so that a corner inside a power carries the label `1`.
Cyclic reduction makes every opposite-sign corner label nontrivial.

Use the star-graph convention of
`kl-unit-exponent-words-inject-when-same-sign-corners-are-free`: a corner
`t^epsilon g t^delta` is an edge `t^(-epsilon) -> t^delta` labelled `g`.
- Opposite-sign corners are loops.
- The `e` same-sign corners form the bipartite two-vertex graph `Theta`.
  - A corner `t g t` is an edge `t^- -> t^+`, with *P-label* `g`.
  - A corner `t^(-1) h t^(-1)` is an edge `t^+ -> t^-`, with *N-label* `h`.

Consider the following conditions.

```text
(D)   every reduced closed path of length two in Theta has nontrivial label;
      equivalently: distinct P-corners carry distinct labels, distinct
      N-corners carry distinct labels, and g h != 1 for every P-label g and
      every N-label h.
(D4)  every reduced closed path of length four in Theta has nontrivial label.
(A2)  no loop label at a vertex v is the label of a reduced closed path of
      length two at v.
```

1. If `e >= 4` and (D) holds, then `<G, t | w>` is aspherical and
   `G -> (G * <t>)/<<w>>` is injective.
2. If `e = 3` and (D), (D4) and (A2) hold, the same conclusion follows.

Nothing is assumed about torsion. The loop coefficients may be involutions or
have any finite order. Stallings' sign-index-two theorem and
Clifford--Goldstein need infinite order at exactly these loops.

## Consequences

- **Length six.** The classes `+++++-` (degree 4) and `++++--` (degree 2)
  have four same-sign corners, so both inject over every group under (D).
  With `kl-length-six-four-sign-change-words-inject`, a violation of variable
  length six needs a coincidence of one of these kinds:
  - two equal same-sign labels;
  - a P-label inverse to an N-label;
  - a finite-order same-sign quotient;
  - an absorbed loop label.
- **The worked Leavitt candidate.** `(L6.1)` of
  `leavitt-length-six-full-support-torsion-candidate` is `++++--`. Its
  P-labels are `x_12(s_1)`, `x_12(t_0)` and the 20-cycle matrix `p`, and its
  N-label is `1`. These are distinct and nontrivial, so part 1 proves its
  injectivity directly, involution loops included.
- **Every length.** Over any group, a violation with at least four same-sign
  corners must repeat a same-sign label, or pair a P-label with the inverse
  of an N-label. For example, a word containing both a `t^2` and a `t^(-2)`
  has a P-label `1` and an N-label `1`, so it does not satisfy (D).
- **Schur kernel.** Asphericity gives a zero Schur kernel
  (`aspherical-adjunction-has-zero-schur-kernel`). No word covered here can
  certify `some-nonsingular-equation-has-nonzero-schur-kernel`.

DERIVATION
kl-four-same-sign-corner-words-weight-proof
