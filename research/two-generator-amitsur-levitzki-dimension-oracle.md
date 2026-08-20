---
rg: 2
id: two-generator-amitsur-levitzki-dimension-oracle
kind: claim
title: Two free-algebra letters enumerate a nonzero polynomial killed by every finite matrix size
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
distinct_from:
  finite-trace-profile-net-is-dimension-free: that replaces all matrix dimensions by a compact space of bounded moments; this detects each actual dimension by a dimension-indexed polynomial identity.
  residual-commutant-supercritical-schur-trigger: that must convert dimension detection into a uniformly sound finite group-word challenge; this is only the exact countable associative-algebra oracle.
  finite-selector-gadget-induction-barrier: that concerns finite-group representation sectors; this is a countable free-algebra construction and asserts no finite presentability.
---

In `C<x,y>`, put

```text
u_j=x y^j x,
p_n=s_(2n)(u_1,...,u_(2n)),                                      (ALO1)
```

where `s_k` is the alternating standard polynomial.  Then

```text
p_n != 0 in C<x,y> for every n>=1,                                (ALO2)
rho(p_d)=0 for every homomorphism rho:C<x,y> -> M_d(C).            (ALO3)
```

Consequently the countably presented unital associative algebra

```text
A_AL=<x,y,q_1,q'_1,q_2,q'_2,... |
       p_n q_n=1, q'_n p_n=1                    (n>=1)>            (ALO4)
```

is nonzero but has no unital finite-dimensional representation.  It is an
exact self-indexing dimension oracle: a `d`-dimensional environment kills the
`d`th instruction without receiving `d` as external input.

This is deliberately not a group or C*-algebra theorem.  The operations in
`p_n` are additive, its degree and coefficient mass grow with `n`, and the
formal inverses in `(ALO4)` need not be bounded operators in any positive
representation.  Turning `(ALO4)` into finite unitary group relations with a
constant normalized-HS gap is a separate open compiler problem.
