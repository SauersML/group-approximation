---
rg: 2
id: finite-permutation-cocycles-cannot-cancel-infinite-isotropy
kind: claim
title: Finite permutation holonomy cannot cancel an infinite stabilizer
distinct_from:
  manzoor-isotropy-has-no-positive-finite-type-corner: that rules out selecting the trivial sector of an infinite regular isotropy representation by a positive finite corner; this rules out canceling isotropy with any finite permutation cocycle.
  relation-cocycles-preserve-full-group-rectangles: that treats finite-rank cocycles pulled back from the principal relation; this allows genuine transformation-group isotropy cocycles but uses positivity of permutation characters.
  regular-isotropy-cocycle-over-hyperlinear-actor-is-ce: that shows exact cancellation over a hyperlinear actor erases the non-CE payload; this proves a stronger impossibility of exact cancellation for finite permutation packets when stabilizers are infinite.
---

Let `Gamma` act pmp on `(X,mu)` with infinite stabilizer `Gamma_x` for
almost every `x`. For every `n<infinity` and every measurable permutation
cocycle

```text
sigma in Z^1(Gamma acting on X,S_n),
```

the decorated relation normalizers

```text
v_g=P_(sigma_g)(u_g tensor 1_n) in M_n(L(R))            (FPC1)
```

cannot have the regular character. Equivalently, some `g!=e` satisfies

```text
(tr_n tensor tau_R)(v_g)>0.                             (FPC2)
```

More generally, if a `U(n)`-valued transformation cocycle is pointwise
traceless on every nonidentity isotropy arrow,

```text
tr_n(b_h(x))=0  for every h in Gamma_x minus {e},       (FPC3)
```

then `|Gamma_x|<=n^2`. Therefore `(FPC3)` is impossible on the Manzoor
non-cohyperlinear IRS, whose stabilizers are infinite almost surely.

Finite-set coinduction, finite color extensions, and finite permutation
holonomy packets are consequently closed. Any finite-rank survivor must use
genuinely complex phase cancellation between different points of each fixed
set; it cannot regularize the isotropy pointwise or by a nonnegative
character.
