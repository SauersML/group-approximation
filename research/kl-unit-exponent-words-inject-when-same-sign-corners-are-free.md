---
rg: 2
id: kl-unit-exponent-words-inject-when-same-sign-corners-are-free
kind: claim
title: Words with unit exponents and degree at least two inject when their same-sign corners are free and absorb no sign-change coefficient
distinct_from:
  kl-length-six-four-sign-change-words-inject: that is the instance with six corners and two same-sign corners; this holds at every length and for any number of same-sign corners.
  kl-small-cancellation-words-inject-every-coefficient-group: that fences by exact syllable repetition and needs at least ten variable occurrences; this fences by the coefficient labels of the star graph and applies at every length.
  leavitt-paired-quotient-passes-relative-weight-test: that proves injectivity for one paired Leavitt quotient; this is a general weight-test theorem for one relator whose exponents are all plus or minus one.
---

Let `G` be any group and `w in G * <t>` cyclically reduced, not a proper power,
with every `t`-exponent `+-1` and degree `m`, `|m| >= 2`.  Of its `n` corners,
`s` lie between opposite signs; they carry the loop coefficients `x_i`.  The
remaining `n - s >= |m|` corners lie between equal signs.  A corner `t g t`
gives an edge `t^- -> t^+` labelled `g`, and a corner `t^(-1) g t^(-1)` an edge
`t^+ -> t^-`.  Let `Theta` be the two-vertex graph of these edges, and let
`phi_v : pi_1(Theta, v) -> G` send a closed path to its label.  If

1. `phi_(t^-)` is injective, equivalently the labels of the `n - s - 1` basic
   cycles freely generate a free subgroup of `G`, and
2. no loop coefficient at a vertex `v` lies in `phi_v(pi_1(Theta, v))`,

then `<G, t | w>` is aspherical and `G -> (G * <t>)/<<w>>` is injective.

With two same-sign corners `y, y'` of the same type, condition 1 says
`y^(-1) y'` has infinite order, and condition 2 excludes `<y y'^(-1)>` at `t^-`
and `<y^(-1) y'>` at `t^+`.  Every window word
`a_1 t b_1 t^(-1) ... a_K t b_K t` of
`kl-cyclic-cover-words-have-an-index-m-core` has exactly this shape, with
`y = b_K` and `y' = a_1`, for every `K`.
