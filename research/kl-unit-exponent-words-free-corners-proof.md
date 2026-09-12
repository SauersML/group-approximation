---
rg: 2
id: kl-unit-exponent-words-free-corners-proof
kind: route
title: Weight the sign-change loops by one and the same-sign graph by zero
target: kl-unit-exponent-words-inject-when-same-sign-corners-are-free
requires: []
---

Use the star-graph convention of
`leavitt-paired-quotient-passes-relative-weight-test`: `t^epsilon g t^delta`
gives an edge `t^(-epsilon) -> t^delta` labelled `g`.  An opposite-sign corner
is a loop, and a same-sign corner is an edge of `Theta` between the two
vertices.

**Counting.**  If `p` and `q` count the `+` and `-` letters, then `m = p - q`
and `s <= 2 min(p, q)`, so `n - s >= |m| >= 2`.

**Weights.**  Put `theta = 1` on every loop and `theta = 0` on every edge of
`Theta`.  The total weight is `s <= n - 2`, which is the relator condition, and
the weights are nonnegative.

**Admissible cycles of weight below two.**
- If the cycle uses no loop, it is a nonempty reduced closed path in `Theta`,
  that is, a nontrivial element of `pi_1(Theta, v)`.  By condition 1 its label
  is not `1`; the two basepoints give conjugate subgroups, so injectivity at
  `t^-` suffices.
- If it uses exactly one loop `x` at `v`, once, rotate it to begin with that
  loop.  The rest is a reduced closed path at `v` in `Theta`, possibly empty.
  Admissibility says its label is `x^(-1)`, so `x in phi_v(pi_1(Theta, v))`.
  Condition 2 excludes this, and the empty path is excluded because `x != 1`.

Every admissible cycle has weight at least two.

**Conclusion.**  `w` is not a proper power, and its degree differs from that of
`w^(-1)`, so the relative presentation is orientable.  The weight test of
Bogley--Pride, *Aspherical relative presentations*, Proc. Edinburgh Math. Soc.
35 (1992), Section 2.2, gives asphericity, and relative asphericity includes
injectivity of `G`.

`Theta` is connected with `n - s` edges on two vertices, so `pi_1` is free of
rank `n - s - 1`.  Since `#(t g t) - #(t^(-1) g t^(-1)) = m`, for `m >= 2` there
are at least two corners of type `t g t`; for `m <= -2`, invert `w`.  With base
edge `z_0` of type `t g t`, a basis at `t^-`
consists of `z_j z_0^(-1)` for the other `t g t` corners and `z_0 z_j` for the
`t^(-1) g t^(-1)` corners.  This gives the free-generation form of condition 1.
