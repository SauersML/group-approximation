---
rg: 2
id: equality-synchronized-lifts-create-two-pair-contours
kind: claim
title: Equality-synchronized pair lifts preserve dimension but create fatal two-pair contours
distinct_from:
  expander-cloud-reduction-preserves-pauli-dimension-gap: that proves ordinary occurrence-cloud degree reduction preserves the dimension witness; this permits additional pair-edge lifts and audits their mixed-contour geometry
  pauli-rectangles-block-naive-relative-c-sixth: that identifies the original eight-syllable rectangle threshold; this proves that synchronized covering or pair-cloud lifts make the relative girth strictly worse
  balanced-pauli-incidence-labeling: that asks for constant pair-edge density on every mixed contour; this exhibits unavoidable mixed contours containing only two pair edges
---

ESTABLISHED.  Consider a bipartite logical incidence graph with X vertices,
Z vertices, and signed pair edges.  Replace a logical X vertex `x` by a fiber
`X_x`, a logical Z vertex `z` by a fiber `Z_z`, and connect each fiber by
equality tests.  Replace a logical pair edge `e=(x,z)` by two or more pair
tests between distinct ports in `X_x` and `Z_z`.

Then the lifted test graph contains a mixed closed contour with exactly two
pair edges.  Consequently:

1. after equality paths are collapsed to the free factors `H_X,H_Z`, the
   contour has relative syllable length at most four, so it cannot satisfy the
   minimum-eight hypothesis of `relative-c-sixth-pauli-incidence-labeling`;
2. as an ordinary contour it violates `(BG2)` of
   `balanced-greendlinger-separates-sign-cosets`, regardless of its ordinary
   length, because the whole cyclic interval contains only two `P` letters.

Thus a growing high-girth pair cloud with equality synchronization cannot
solve either the relative or balanced occurrence-labeling problem.

## Proof of the contour obstruction

Choose two lifted pair edges of `e`,

```text
u_0 -- v_0,   u_1 -- v_1,
u_i in X_x,   v_i in Z_z.
```

Since the two equality fibers are connected, choose simple equality paths
from `u_0` to `u_1` and from `v_0` to `v_1`.  The two pair edges together
with these paths form a closed mixed walk.  Removing spurs leaves a mixed
closed contour with no more pair edges than the original walk, hence exactly
two in the nondegenerate case.  In the relative free product its cyclic word
has the form

```text
p_0 h_Z p_1^(-1) h_X,                                (ESL1)
```

with zero or nonzero equality syllables.  Its relative length is at most
four; a trivial equality syllable only shortens it.

For the ordinary balanced condition, take the whole cyclic contour as the
interval in `(BG2)`.  It contains at most two `P` letters and has length
`|r|`, contradicting `|r| <= beta |r|` for every `beta<1`.  Making the
equality paths long, making the pair cloud high-girth, or assigning a larger
covering sheet does not change this count.

## Same-Hilbert dimension preservation is not the failure

The lifted game itself can retain the robust Pauli dimension bound.  Put
fixed-gap bounded-degree equality expanders on every fiber and distribute the
copies of each old pair test with bounded regular weights.  From a strategy
of rejection `delta`, the expander Poincare inequality chooses one
representative reflection per logical observable on the **same Hilbert
space**, with average squared deviation `O(delta)`.  Replacing the endpoints
in one copied old test changes its correlation by `O(sqrt(delta))`.  Averaging
over logical tests decodes a strategy for the original game with rejection
`O(delta+sqrt(delta))`.  Perfect strategies copy identically across fibers.

Hence the dimension lower bound survives exactly as in
`expander-cloud-reduction-preserves-pauli-dimension-gap`.  The obstruction is
purely combinatorial: the equality synchronization which enables that decoder
also creates `(ESL1)`.

## Covering-lift dichotomy

More generally, contract every connected equality fiber of any lift.  All
lifts of one base pair edge become parallel edges between the same two
contracted vertices.

- If there are at least two lifts, they give the two-edge contour `(ESL1)`.
- If there is only one, contraction retains the original base incidence
  graph and therefore retains every original Pauli rectangle.
- If the fibers are left disconnected so that a covering lift can have large
  girth, expander/Poincare synchronization no longer identifies the sheets on
  one Hilbert space; the established same-Hilbert decoder does not apply.

Thus edge-type covers, replacement products, and pair-cloud lifts cannot
raise the **contracted relative girth** while also synchronizing each logical
fiber by equality tests.

## Fixed-q point--plane low-degree tests do not evade the dichotomy

The point--plane incidence used by the quantum low-degree Pauli test has
abundant rectangles once the ambient affine dimension is at least three: two
distinct points determine a line, and two distinct affine planes containing
that line give a point--plane--point--plane four-cycle.  Ordinary occurrence
degree reduction therefore lands in the threshold-rectangle obstruction
`finite-offset-pauli-rectangles-violate-relative-gr-sixth`.

A high-girth covering of the point--plane incidence has the same alternatives
as above.  Equality-connect the lifted copies of every base point and plane,
and two lifts of one incidence edge give `(ESL1)`.  Leave the fibers
disconnected, and the lifted point answers are no longer one measurement for
each point of the base affine space.  The published low-degree decoder
constructs a single global low-degree measurement from consistency on that
base point/plane geometry; it does not state a cover-invariant decoder which
identifies distinct lifted point fibers on the same Hilbert space.  Thus a
cover may still be a new research direction, but its soundness is not inherited
from the low-degree theorem without an additional synchronization theorem.

This audit uses only the incidence and decoder interface, not the internal
quantitative constants of the low-degree test.

Primary source for that interface: A. Natarajan and T. Vidick, *Low-degree
testing for quantum states, and a quantum entangled games PCP for QMA*,
arXiv:1801.03821, especially the point/plane test description and the global
low-degree measurement in the soundness analysis.

## Attempts

The audited positive attempt replaced every logical pair test by a growing
high-girth bipartite pair cloud and placed fixed-gap expanders on both endpoint
fibers.  Its game-theoretic soundness and same-Hilbert dimension decoding are
valid.  It dies at `(ESL1)`: any two cloud edges already form a two-pair mixed
contour through the equality fibers.  A synchronizing code could escape only
if it decodes logical observables without placing all code coordinates in one
connected equality component; that would require a new product/linearity
decoder, not an equality-cloud lift.
