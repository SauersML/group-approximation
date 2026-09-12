---
rg: 2
id: disjoint-footprint-decoders-force-kaplansky-failure
kind: claim
title: A strict pair whose decoder never multiplies encoder outputs with overlapping footprints forces a matrix direct-finiteness failure
distinct_from:
  low-degree-strict-pairs-have-one-sided-linear-parts: that bounds the degree product below q; this bounds no degree, and over F_2 it covers decoders of every degree whose monomials multiply encoder outputs with pairwise disjoint essential footprints.
  low-degree-strict-automata-force-matrix-kaplansky-failure: that reaches the same failure under deg sigma * deg tau < q, which over F_2 forces both rules linear; this reaches it under a footprint condition on decoder monomials, with no degree bound.
  invariant-output-automata-have-only-nonlinear-decoders: that rules out linear decoders under an even-order output symmetry by augmentation; this shows every decoder with disjoint monomial footprints, linear ones included, makes a strict pair a matrix Kaplansky pair, with no symmetry hypothesis.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `F = F_q`, `G` a group, and `tau`, `sigma` automata on `(F^n)^G` with `sigma o tau = id`.
Use reduced representatives, with every exponent below `q`.
- **Encoder.** Rules `mu_j` with essential footprints `F_j`, the memory cells occurring in `mu_j`.
- **Decoder.** Rules `nu_i` in the variables `Y_(s,j)`, the encoder output of track `j` at offset `s`.

**Condition (DF).** Every monomial of every `nu_i` is multilinear in the `Y`-variables, and any two
distinct variables `Y_(s,j)`, `Y_(s',j')` in a common monomial satisfy `s F_j ∩ s' F_(j') = ∅`.

**Theorem.** Under (DF), if `tau` is not surjective, then `M_n(F_q[G])` is not directly finite, so
`M_(nk)(F_p[G])` is not directly finite for `q = p^k`.

**Special cases and consequences.**
- **Affine decoders.** Every affine decoder satisfies (DF). A strict automaton with an affine left
  inverse is a matrix Kaplansky pair, whatever the encoder.
- **Hosts with stably finite `F_p[G]`.** There, every strict pair over `F_q^n` needs a decoder
  monomial that multiplies two encoder outputs reading a common essential cell, or that uses a
  power (`q > 2`). Over `F_2` this is a nonlinear decoder term at a forward coincidence that both
  encoder copies actually read. Coincidences merely present in the table are not enough.

**Why.** Under (DF) the formal composite is a product of reduced polynomials in pairwise disjoint
variable sets, summed, so it is reduced. A reduced polynomial equal to `X_(g,i)` on `F_q`-points
is `X_(g,i)`, so the identity is formal, and
`formal-polynomial-strict-pairs-need-unstable-linearization` applies.

Artifact, Section 5.
