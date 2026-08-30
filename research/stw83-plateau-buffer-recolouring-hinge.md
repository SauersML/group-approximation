---
rg: 2
id: stw83-plateau-buffer-recolouring-hinge
kind: claim
title: Plateau-local corner colours would solve the canonical family, but block-diagonal separation cannot provide them
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
distinct_from:
  stw83-canonical-circle-toeplitz-dimension-two-bound: that spends a third global colour; this identifies the exact support condition which would remove it and proves a no-go for the most direct whole-corner implementation.
---

Fix `N>=1` and

```text
A_N=C*(S^N tensor 1, K tensor C(T)).
```

In the coefficient-valued Brake--Winter decomposition, let `h` and
`tilde(h)` be a sufficiently late nested pair of finite-rank quasicentral
contractions, with `tilde(h)h=h`, and let

```text
D=supp(h) A_N supp(h)=M_r(C(T)).
```

Let `p<=supp(h)` be a nonzero plateau projection on which both `h` and
`tilde(h)` are one.  Suppose that, for every finite set and tolerance, the
inner compression through `D` can be approximated by two finite-dimensional
order-zero colours `eta^(0),eta^(1)` such that

```text
eta^(0)(G^(0)) subset pDp,
eta^(1)(G^(1)) subset D.                                (PL)
```

The plateau may depend on the finite set and may be separated from the
transition band by an arbitrarily long scalar buffer.  Then

```text
dim_nuc(A_N)=1.                                          (1)
```

Condition `(PL)` cannot be obtained by a uniform block-diagonal
approximation of the whole corner.  More precisely, if `0<p<1` is a constant
projection in `D=M_r(C(T))`, there is no net of two-colour approximations of
`id_D` in which

```text
eta^(0)(G^(0)) subset pDp,
[p,eta^(1)(G^(1))]=0.                                   (BD)
```

Thus a successful plateau/buffer proof must be finite-set adaptive and its
second inner colour must genuinely cross the plateau boundary.  Merely
putting one circle colour in the plateau and leaving the other block diagonal
would force a false zero-dimensional approximation of a complementary circle
corner.
