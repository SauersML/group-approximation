---
rg: 2
id: sl3-coset-lamp-collapses-from-projective-transfer
kind: route
title: Collapse the recursive arithmetic lamp mark through one projective commutator
target: non-hyperlinear-group
requires:
  - sl3-codense-coset-lamp-recursive-host
  - sl3-two-point-lamp-mark-is-single-rcc-scalar
  - projective-commutant-transfer-for-arithmetic-pair
  - higman-bypass-needs-only-fg-recursive-nonhyperlinear
---

Assume canonical microstates of the recursively presented arithmetic lamp
host.  Its actor coordinates are approximate representations of
`SL_3(Z[1/2])`, and the base lamp `c` projectively centralizes every fixed
generator of `SL_3(Z)` because the root-stabilizer relators have vanishing
defect.  Projective transfer gives

```text
1-|tr([c,h])|^2 -> 0.
```

The two-point seed is `m_0=[c,h]`.  By `(RCS3)--(RCS4)`, projective scalarity
of `m_0` and the D8 relator imply `||J-I||_2->0`.  But the exact infinite
model has `J!=1`, so canonical microstates require
`||J-I||_2->sqrt(2)`.  Contradiction.  The recursive lamp host is therefore
nonhyperlinear, and the post-proof Higman bypass supplies a finitely
presented nonhyperlinear overgroup.
