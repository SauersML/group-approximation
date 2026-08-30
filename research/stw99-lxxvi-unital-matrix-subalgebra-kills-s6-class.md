---
rg: 2
id: stw99-lxxvi-unital-matrix-subalgebra-kills-s6-class
kind: claim
title: A unital matrix subalgebra kills the unstable S6 scalar clutching class
distinct_from:
  stw99-lxxvi-unital-z-subalgebra-kills-unstable-scalar-classes: that uses K-stability of the Jiang-Su algebra and applies to every stably trivial scalar class; this uses only the finite stable range at pi_5 and excludes every unital matrix subalgebra of size at least two.
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Let `D` be a unital C*-algebra.  If there is a unital embedding

```text
M_k -> D
```

for some `k>=2`, then the scalar-extension image of the nonzero class

```text
alpha in pi_5(U(2))=Z/2
```

is zero in

```text
pi_5(U(M_2(D))).                                        (1)
```

Indeed, the scalar map factors at the matrix-unitary level as

```text
U(2) -> U(M_2(M_k))=U(2k) -> U(M_2(D)),
u |-> u tensor 1_k.                                    (2)
```

The first map in (2) already kills `alpha`.

Consequently, any coefficient for the surviving `S^6` clutching witness in
Problem LXXVI must contain no unital copy of `M_k` for any `k>=2`, in
addition to containing no unital copy of `Z`.  The restriction `k>=2` is
sharp for this argument: for `k=1`, (2) is the identity on `U(2)` and
`alpha` is nonzero.
