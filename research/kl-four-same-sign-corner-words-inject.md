---
rg: 2
id: kl-four-same-sign-corner-words-inject
kind: claim
title: A nonsingular word with at least four coincidence-free same-sign corners injects over every group
invalidates: [leavitt-kl-violation-from-distinct-same-sign-labels]
distinct_from:
  kl-unit-exponent-words-inject-when-same-sign-corners-are-free: that needs the same-sign labels to generate a free group of rank e-1 and no absorbed loop, which is the only available fence at two same-sign corners; this needs only four same-sign corners that close no trivial 2-cycle, however the other same-sign labels coincide (three with two extra short-cycle conditions).
  kl-length-six-four-sign-change-words-inject: that settles the two length-six classes with two same-sign corners; this settles the remaining classes +++++- and ++++--, which have four.
  leavitt-paired-quotient-passes-relative-weight-test: that proves injectivity for the paired quotient of one specific Leavitt candidate from its specific labels; this proves injectivity for every word with four coincidence-free same-sign corners over every group, and covers that candidate directly.
  kl-small-cancellation-words-inject-every-coefficient-group: that fences by exact syllable repetition from ten variable occurrences on; this fences by coincidences among star-graph labels at every length.
---

Let `G` be any group and `w in G * <t>` cyclically reduced, not a proper
power, with `deg_t(w) = m != 0`. Split every power `t^(+-k)` into single
letters, so that a corner inside a power carries the label `1`. Cyclic
reduction makes every opposite-sign corner label nontrivial.

Use the star-graph convention of
`kl-unit-exponent-words-inject-when-same-sign-corners-are-free`: a corner
`t^epsilon g t^delta` is an edge `t^(-epsilon) -> t^delta` labelled `g`.
- Opposite-sign corners are loops.
- The `e` same-sign corners form the bipartite two-vertex graph `Theta`:
  - a corner `t g t` is an edge `t^- -> t^+`, with *P-label* `g`;
  - a corner `t^(-1) h t^(-1)` is an edge `t^+ -> t^-`, with *N-label* `h`.

A reduced closed path of length two in `Theta` has label `g g'^(-1)`, `h h'^(-1)`
or (a conjugate of) `g h`. Call a same-sign corner *heavy* if it lies on such a
path with trivial label: another corner of the same type carries the same
label, or a corner of the other type carries the inverse label. Otherwise it
is *light*. Let `r` be the number of light corners.

1. If `r >= 4`, then `G -> (G * <t>)/<<w>>` is injective, and every reduced
   spherical picture over `<G, t | w>` is empty.
2. If `r = 3`, the same conclusions hold provided:
   - (D4) every reduced closed path of length four in `Theta` made of light
     edges has nontrivial label; and
   - (A2) no loop label at a vertex `v` is the label of a reduced closed path
     of length two at `v` made of light edges.

Nothing is assumed about torsion: the loop coefficients may be involutions or
have any finite order. Stallings' sign-index-two theorem and
Clifford--Goldstein need infinite order at exactly these loops. The heavy
corners may have any coincidence pattern.

## Consequences

- **Length six.** The classes `+++++-` (degree 4) and `++++--` (degree 2) have
  four same-sign corners. When no two of them coincide, both inject over
  every group. With `kl-length-six-four-sign-change-words-inject`, a
  length-six violation needs a coincidence:
  - two equal same-sign labels,
  - a P-label inverse to an N-label,
  - a finite-order same-sign quotient, or
  - an absorbed loop label.
- **The worked Leavitt candidate.** `(L6.1)` of
  `leavitt-length-six-full-support-torsion-candidate` is `++++--`. Its
  P-labels are `x_12(s_1)`, `x_12(t_0)` and the 20-cycle matrix `p`, and its
  N-label is `1`. All four corners are light, so part 1 proves injectivity
  directly, involution loops included.
- **Every length.** Over any group, a violating word has at most three light
  same-sign corners. So every other same-sign corner repeats a label of its
  own type or inverts a label of the other type, and violations are
  coincidence-saturated. Label-`1` corners inside powers coincide as soon as
  there are two of one type, or one of each type. This matches the
  near-periodicity forced by `kl-small-cancellation-words-inject-every-coefficient-group`.
- **Schur kernel, conditionally.** Bogley--Pride state that an orientable
  relative presentation with no nonempty reduced spherical picture has an
  aspherical relative 2-complex; this was not read at source. Granting it,
  `aspherical-adjunction-has-zero-schur-kernel` gives a zero Schur kernel, so
  no word covered here can certify
  `some-nonsingular-equation-has-nonzero-schur-kernel`.

## Provenance and novelty

- **Weight conditions.** These follow Bogley--Pride, Proc. Edinburgh Math.
  Soc. 35 (1992), Section 2.2, through the verbatim restatement in
  Ahmad--Al-Mulla--Edjvet, arXiv:1604.00163v2. Bogley--Pride was not reached.
  The derivation proves injectivity directly by a curvature count, so their
  theorem that asphericity gives an embedding is not used.
- **What was checked.** Per Klyachko--Thom, Algebr. Geom. Topol. 17 (2017),
  Remark 1.2, Kervaire--Laudenbach is solved over arbitrary groups for
  lengths three, four and five (Howie; Edjvet--Howie; Evangelidou). No
  length-six theorem over arbitrary groups was found.
- **Novelty unchecked.** Edjvet--Juhász, *Non-singular equations over groups*
  I (Algebra Colloq. 18 (2011)) and II (Comm. Algebra 38 (2010)), treat
  torsion and were not read.

DERIVATION
kl-four-same-sign-corner-words-weight-proof
