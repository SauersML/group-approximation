---
rg: 2
id: leavitt-even-region-short-atlas-has-area-ten
kind: claim
title: The even-region short-coefficient sector of the Leavitt three-gate picture has area at least ten
artifacts:
  - research/artifacts/leavitt-eight-cell-curvature-core-audit-2026-08-21.md
distinct_from:
  leavitt-short-atlas-does-not-close-six-cells: that exhausts the six-vertex ribbon cores; this classifies the eight-vertex cores after curvature forces bipartiteness.
  leavitt-three-gate-square-picture-area-eight: that retains only three square gates and proves a lower bound of eight; this uses the enlarged V4-by-V4 short coefficient atlas and excludes area eight in the even-region sector.
---

Let

```text
Q=V_4(h_0,h_2) * V_4(k_0,k_1) * F(h_1,k_2)
```

be the strengthened coefficient quotient from
`leavitt-short-atlas-does-not-close-six-cells`.  There is no reduced
coefficient-boundary relative picture with at most eight relator vertices
whose internal coefficient regions are trivial in `Q`.

At area eight, five internal regions must be trivial and the sixth is the
outer boundary.  Every `Q`-trivial cyclic word has even length.  Since the
sum of the six face lengths is `24`, the outer face is even too.  Thus the
cubic planar ribbon core is bipartite.  Up to independent permutations of
the two four-vertex color classes there are twelve nonnegative `4 x 4`
adjacency matrices with every row and column sum three; connected planarity
leaves exactly five core types.  Enumerating their planar rotations,
sign-compatible relator slots, and two relator colors gives no disk.

Consequently every actual area-eight kernel picture must already use a
coefficient identity outside the short atlas in an internal region.  The
shortest residual even-region words have reduced `Q`-length eight; none is
an identity in `G_0*G_1` after expansion of `h_1=q_0p_1` and
`k_2=p_0e_1` and root-word reduction.

The scope is exact: this proves a rigorous area-ten lower bound for the
entire even-region short-atlas sector.  It does not exclude an area-eight
picture whose longer Leavitt coefficient identity destroys the parity
reduction.

