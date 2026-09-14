---
rg: 2
id: kl-length-six-four-sign-change-words-inject-proof
kind: route
title: Put unit weight on the four sign-change loops and none on the two parallel edges
target: kl-length-six-four-sign-change-words-inject
requires: []
---

**Classes.**  Degree two at length six means four `+` and two `-`.  Two
cyclically adjacent `-` letters give `++++--`, which has two sign changes.
Otherwise the two `-` sit at cyclic distance two or three, giving `+++-+-` or
`++-++-`.  Each `-` letter is flanked by `+` letters, so there are exactly four
opposite-sign corners, and both remaining corners lie between two `+` letters.

**Star graph.**  Use the convention of
`leavitt-paired-quotient-passes-relative-weight-test`: a subword
`t^epsilon g t^delta` gives an edge from `t^(-epsilon)` to `t^delta` labelled
`g`.  A corner `t g t^(-1)` gives a loop at `t^-`, a corner `t^(-1) g t` a loop
at `t^+`, and a corner `t g t` an edge from `t^-` to `t^+`.  So the star graph
has the four loops `x_i` and two parallel edges `y, y'`, both oriented from
`t^-` to `t^+`.

**Weights.**  Put `theta = 1` on the loops and `theta = 0` on `y, y'`.  The
relator has six corners and total weight `4 = 6 - 2`, which is the relator
condition.  The weights are nonnegative.

**Admissible cycles.**  A reduced closed path of weight less than two traverses
at most one loop, once.
- If it traverses none, it alternates `y` and `y'^(-1)`.  Its label is a nonzero
  power of `y y'^(-1)` or of `y^(-1) y'`, and these have the order of
  `y^(-1) y'`, which is infinite.  So the label is nontrivial.
- If it traverses one loop `x` once, rotate the cycle to start at that loop.
  The rest is a zero-weight closed path at the same vertex, with label a power
  of `y y'^(-1)` at `t^-` or of `y^(-1) y'` at `t^+`.  Admissibility would put
  `x^(+-1)` in one of those cyclic groups, which is excluded; the empty rest is
  excluded because `x != 1`.

Every admissible cycle therefore has weight at least two.

**Conclusion.**  `w` is not a proper power, and its degree two differs from the
degree of `w^(-1)`, so the relative presentation is orientable.  The weight
test of Bogley--Pride, *Aspherical relative presentations*, Proc. Edinburgh
Math. Soc. 35 (1992), Section 2.2, as already used in
`leavitt-paired-quotient-passes-relative-weight-test`, gives asphericity.
Relative asphericity includes injectivity of the coefficient group.

A finite-order `x_i` cannot equal a nonzero power of an infinite-order element,
which gives the stated special case.
