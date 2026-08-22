---
rg: 2
id: leavitt-d4-l14-fifteen-n0214-fence-proof
kind: route
title: Exhaust both normal fifteen-winner 0;214 boundary branches
target: leavitt-d4-l14-fifteen-n0214-is-fenced
requires:
  - leavitt-d4-l14-fifteen-n0214-carriers-are-explicit
  - maximal-noncrossing-forest-criterion
---

Apply the coordinate-preserving all-maximal forest semiring to both exact
middle-carrier branches.  It gives `70` joint carrier states in branch I and
`38` in branch II.  For every state, transform the literal raw boundary, take
all normalized cyclic cuts, append the fresh target coordinate in all four
copies, and enumerate all coarsening-maximal cancellation forests.

The Q-first replay, MSI job `16683063`, returned

```text
             branch I   branch II
carrier states      70          38
augmented words      4           4
boundary states    280         152
q nonempty            0           0
unresolved            0           0
```

In fact, after each joint carrier substitution the transformed coefficient
boundary is empty; the four augmented words are just the four choices of
target copy for `q^-1`, and Tietze closure eliminates `q` in every state.
Thus the boundary itself is the identity throughout both exhaustive branches.
