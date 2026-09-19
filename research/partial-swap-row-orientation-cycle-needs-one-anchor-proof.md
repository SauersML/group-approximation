---
rg: 2
id: partial-swap-row-orientation-cycle-needs-one-anchor-proof
kind: route
title: Quotient row signs, exhibit the stationary cycle twist, and charge it at the D8 anchor
target: partial-swap-row-orientation-cycle-needs-one-anchor
requires:
  - centralizing-d8-word-anchors-relative-row-orientation
---

For a block row `D=diag(A,B)`, multiplication by a scalar sign changes
`AS-SB` by the same sign and leaves `DJDJ` unchanged.  Multiplication by the
grading `Z=diag(I,-I)` changes the residual to `AS+SB`; the parallelogram
identity gives

```text
||AS-SB||_2^2+||AS+SB||_2^2=4||S||_2^2.
```

Thus only the relative grading bit is load-bearing.

Any finite comparison graph whose edges constrain only ratios has equations
`t_v t_w=sigma_(vw)`.  Multiplying all `t_v` by `-1` preserves every edge.
The ambiguity is realized exactly on an arbitrary multiplicity space by
placing the same commuting involution at every vertex, so it is not an
artifact of scalar notation or approximate analysis.

Finally `centralizing-d8-word-anchors-relative-row-orientation` supplies one
ordinary-word absolute anchor: its intended word `e` commutes with the D8
swap and its relative twist obeys `[ze,j]=y`.  A separated mark therefore
charges the simultaneous wrong twist at dimension-independent scale.  This
proves that one anchor is necessary and sufficient at the orientation-bit
level; the construction of relative comparisons for selected nonlinear row
types is a separate compiler problem.
