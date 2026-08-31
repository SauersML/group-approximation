---
rg: 2
id: long-router-square-energy-cannot-control-endpoint-frame
kind: claim
title: Vanishing SU(2) router energy can hide a macroscopic endpoint rotation
distinct_from:
  head-retention-forces-distance-from-every-global-frame: that proves a head-retaining tuple must have genuine frame curvature; this shows why integrating small local curvature along a growing router is not dimension-free
  jacobson-projective-two-sheet-actions-collapse: that controls coefficient rotations satisfying the full fixed presentation; this is a counterexample to a growing-word covariance compiler, not a Jacobson microstate
  two-raw-roots-have-a-uniform-full-carrier-gap: that gives a uniform gap once both raw covariance tests are available; this proves those tests cannot be recovered from a long path by naive energy accumulation
---

For every even `L` there are unitaries `C_L,W_L` on
`C^L tensor C^2` such that `W_L` is a non-scalar `SU(2)` field and

```text
||C_LW_LC_L^(-1)-W_L||_2=2 sin(pi/L),                  (LRS1)

sum_(j=0)^(L/2-1)
 ||C_L^(j+1)W_LC_L^(-(j+1))
   -C_L^jW_LC_L^(-j)||_2^2
 =2L sin^2(pi/L) ->0,                                  (LRS2)

||C_L^(L/2)W_LC_L^(-L/2)-W_L||_2=2.                   (LRS3)
```

Consequently there is no dimension-independent constant `B` for an
endpoint estimate of the form

```text
||W_L^(endpoint)-W_L||_2^2
 <= B sum_(router edges)||local covariance defect||_2^2. (LRS4)
```

The linear telescoping loss has the correct scale: a word of length
`Theta(L)` can accumulate a macroscopic rotation from local errors
`Theta(1/L)`.

Thus, if a raw-root covariance term is represented by a conjugating word
whose length grows with the Toeplitz cutoff, neither direct telescoping nor
an unweighted Hilbert--Schmidt square-function yields the required uniform
compiler. A successful Jacobson argument must use the fixed two-root
Kazhdan packet directly or a head-localized weighted identity. The clock
field itself is not a head-retaining Jacobson microstate.

DERIVATION
su2-clock-field-has-zero-router-energy-proof
