---
rg: 2
id: nonedge-spectrum-cannot-descend-to-forty-two-chart
kind: claim
title: The nonedge commutator spectrum cannot descend to the forty-two-point chart
distinct_from:
  no-native-arithmetic-relator-breaks-the-bernoulli-quotient: that isolates the nonedge commutator as the first canonical-trace anti-relation; this proves that even arbitrary Borel functional calculus of that word has a fixed stabilizer-covariance defect and therefore cannot itself supply a chart atom.
  native-forty-two-shell-has-a-noncommuting-pair: that proves the two shell lamps do not commute and computes the additive commutator norm; this computes the point-stabilizer action on their group commutator and the exact HS defect of every one-word spectral projection.
  finite-bernoulli-site-decoder-has-schreier-error-floor: that obstructs finite factors of the commuting Bernoulli lamp algebra by the global Schreier gap; this works in the native noncommutative graph-product regular algebra and already fails at the finite-index chart stabilizer.
  actor-algebra-cannot-wordize-shell-phase-tag: that proves a constant-line distance for linear actor-algebra words on an already decoded shell PVM; this rules out nonlinear spectral cuts of the raw nonedge word before a shell PVM has been decoded.
---

ESTABLISHED. Put

```text
C=SL_3(Z),       h=diag(2,1,1/2),
D=C cap h C h^(-1),
x=hC,            y=h^(-1)C,
kappa=[c_x,c_y]                                          (KSD1)
```

in the native Hecke graph-wreath group `G_cc`. Let

```text
d=x_21(1) in C.                                          (KSD2)
```

Then `d in D`, so `d` fixes the chart basepoint `x`, but `d` does not fix
`y`. Indeed

```text
h^(-1)d h=x_21(2) in C,       h d h^(-1)=x_21(1/2) notin C. (KSD3)
```

Writing `z=dy`, the two pairs `{x,y}` and `{x,z}` consist of distinct
nonedges. Graph-product normal form gives

```text
<kappa> cap <d kappa d^(-1)>={1}.                       (KSD4)
```

More explicitly, `kappa=(c_xc_y)^2` and
`d kappa d^(-1)=(c_xc_z)^2`; every nonzero power is cyclically reduced and
has support respectively `{x,y}` and `{x,z}`.

Let `tau` be the canonical trace of `L(G_cc)`. For every projection

```text
E in W^*(kappa),             tau(E)=t,                  (KSD5)
```

Fourier support and `(KSD4)` give the exact independence identity

```text
tau(E d E d^(-1))=t^2.                                  (KSD6)
```

Therefore

```text
||d E d^(-1)-E||_2^2=2t(1-t).                           (KSD7)
```

This applies to arbitrary Borel spectral projections of `kappa`, not only
to group-algebra polynomials. In particular the only `D`-invariant
projections in `W^*(kappa)` are `0` and `1`: invariance places `E` in

```text
L(<kappa>) cap L(<d kappa d^(-1)>)=C.                  (KSD8)
```

A base atom for the chart `C/D` must be `D`-invariant, and its `42`
`C`-conjugates must have proper positive trace. Hence no polynomial,
continuous, or Borel spectral construction from the single anti-relation
`kappa` can be the missing forty-two-chart atom.

There is also a canonical-microstate version. If `rho_n` are canonical
normalized-HS microstates of `G_cc`, `Delta` is a Borel arc whose boundary
has Haar measure zero, and

```text
E_n=1_Delta(rho_n(kappa)),       t=Leb(Delta),           (KSD9)
```

then fixed Laurent-polynomial approximation and the canonical word moments
give

```text
tr(E_n)->t,
||rho_n(d)E_n rho_n(d)^*-E_n||_2^2 ->2t(1-t).           (KSD10)
```

Thus increasing spectral resolution or allowing matrix-dependent exact
spectral cuts does not remove the leakage.

The viable refinement is now precise. One must use the joint algebra of the
entire finite `D`-orbit of pair commutators and produce a genuinely
`D`-invariant nonlinear projection there, then prove that its `42`
`C`-translates are orthogonal and that section transport controls their
`(EDA11)` leakage. Averaging one spectral projection over that orbit is not
a projection because the conjugate cyclic algebras do not commute. The
single `kappa` seam, despite excluding the Bernoulli quotient, cannot defeat
independent chart refinement by itself.
