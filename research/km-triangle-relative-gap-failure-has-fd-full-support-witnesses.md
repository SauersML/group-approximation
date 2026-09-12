---
rg: 2
id: km-triangle-relative-gap-failure-has-fd-full-support-witnesses
kind: claim
title: The Kac-Moody triangle has finite-dimensional full-ideal-support witnesses with arbitrarily low relator energy
distinct_from:
  km-triangle-relator-kernel-has-no-relative-gap: that obtains arbitrary unitary witnesses from failure of relative property T and explicitly leaves their finite dimensionality open; this upgrades them to genuine finite-dimensional representations and identifies their ideal support projection.
  exhausting-ideal-reservoirs-have-lift-or-quotient-separator: that gives the lift-versus-separator alternative for exhausting reservoirs; this spectral degeneration occurs independently and hence cannot distinguish the two branches of that alternative.
  finite-packet-triangle-repair-is-ideal-block-choi-feasibility: that uses an arbitrary finite packet and its central ideal support; this constructs packets for which that support is the identity while every prescribed finite relator reservoir has arbitrarily small Rayleigh energy.
---

**ESTABLISHED.**  In the explicit Kac--Moody triangle write

```text
1 -> K -> G_0 -> Lambda ->1,
A=C^*(G_0),       I=ker(A->C^*(Lambda)).                  (FDR1)
```

Assume the established inputs already recorded for this instance:

- `G_0` is finitely generated virtually free, hence `C^*(G_0)` is RFD;
- `Lambda` is infinite, finitely generated and simple, hence has no nontrivial
  finite-dimensional unitary representations;
- `(G_0,K)` does not have relative property `(T)`.

Then for every finite `F subset G_0` and every `epsilon>0` there are a genuine
finite-dimensional unitary representation `rho:G_0->U(D)` and a unit vector
`xi` such that

```text
H_rho^K={0},          max_(g in F)||rho(g)xi-xi||<epsilon. (FDR2)
```

Let `J=rho(I)` and let `z_rho` be the unit of this finite-dimensional ideal.
Then

```text
z_rho=1_D.                                                   (FDR3)
```

Thus the almost-invariant vector is not hidden in the scalar quotient block:
it lies in a packet whose entire Hilbert space is the ideal block.

In particular, fix a finite relator reservoir

```text
B_W={a(n_j^(+-1)-1)b:a,b in W, 1<=j<=r}                   (FDR4)
```

from `km-triangle-relator-kernel-has-no-relative-gap`.  For every `eta>0`
there are `rho,xi` as above, still with `z_rho=1`, for which

```text
sum_(x in B_W)||rho(x)xi||^2<eta.                          (FDR5)
```

Equivalently the finite-dimensional positive relator Laplacian

```text
Delta_(rho,W)=sum_(x in B_W)rho(x)^*rho(x)
```

has a Rayleigh quotient below `eta` on a full-ideal-support representation.
This strengthens the spectral no-go from arbitrary representations to the
same finite-dimensional packets used by the ideal-block Choi problem.

Proof: `rfd-upgrades-relative-gap-failure-to-full-support-fd-witnesses`.

**Interpretation.**  These low-spectrum packets do not follow from failure of
a uniform relator depth; they exist before that question is asked.  Therefore
the occurrence of `(FDR5)` cannot decide whether the exhausting reservoir
distances tend to zero (and give a lift) or remain positive (and give a
quotient separator).  In particular one must not turn a degenerating signed
Choi certificate into a positive low-spectrum vector without an additional
positivity theorem.

DERIVATION
rfd-upgrades-relative-gap-failure-to-full-support-fd-witnesses
