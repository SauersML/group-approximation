---
rg: 2
id: finite-kernel-window-has-maximally-moving-zero-mode
kind: claim
title: Every finite presentation-kernel window has an exact finite moving zero mode
distinct_from:
  free-presentation-kernel-has-no-conjugation-folner-exhaustion: that rules out asymptotically invariant coefficient weights on the whole kernel; this constructs an exact finite-dimensional false zero mode for each fixed kernel window.
  simple-map-quotient-has-rigid-fd-restriction: that says agreement on all of `K` forces agreement on all of `F`; this proves that replacing all of `K` by any finite subset destroys the conclusion maximally.
  leavitt-positive-rank-intertwiner-retention: that asks for a growing-window almost-reducing sector; this shows why both growth and almost reduction are load-bearing.
---

**ESTABLISHED.** Let `F` be a finitely generated free group, let
`K normal F`, fix `f_0 in F\K`, and let `R subset K` be finite. There are a
finite-dimensional exact unitary representation `pi_R:F->U(H_R)` and a unit
vector `xi_R` such that

```text
pi_R(k)xi_R=xi_R                   for every k in R,    (FKW1)
<pi_R(f_0)xi_R,xi_R>=0.                                  (FKW2)
```

Equivalently, for every choice of positive weights on `R`, the finite kernel
energy

```text
A_R=sum_(k in R) alpha_k(pi_R(k)-1)^*(pi_R(k)-1)       (FKW3)
```

has an exact zero eigenvector with maximal displacement

```text
||(pi_R(f_0)-1)xi_R||=sqrt(2).                         (FKW4)
```

The construction is a finite coset permutation representation. Put
`H=<R>`. Since `H<=K` but `f_0 notin K`, one has `f_0 notin H`. Hall subgroup
separability for finitely generated free groups gives a finite-index subgroup
`L<=F` with

```text
H<=L,                     f_0 notin L.                 (FKW5)
```

Let `pi_R` be the permutation representation on `ell^2(F/L)` and
`xi_R=delta_L`. Every element of `R` fixes the base coset, while `f_0L!=L`,
so `(FKW1)--(FKW4)` follow.

This remains true when `K` is finitely normally generated: `(FKW1)` fixes
the relators on one vector, not on its full `F`-cyclic span, and conjugate
relators move that vector to other cosets. Thus a fixed presentation and
property `(T)` of `F/K` do not create a finite kernel-energy gap on the
candidate vector. The retention route must simultaneously let the kernel
window grow and prove `(IR1)` relative to the retained rank; either ingredient
without the other admits these exact finite models.

DERIVATION
finite-kernel-window-moving-zero-mode-proof
