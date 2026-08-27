---
rg: 2
id: two-equivariant-shell-pvms-have-independent-coordinate-escape
kind: claim
title: Two exactly equivariant SL3 shell PVMs retain an independent-coordinate Gram escape
artifacts:
  - research/artifacts/sl3-two-shell-independent-coordinate-escape-2026-08-22.md
distinct_from:
  five-parahoric-overlap-saturations-give-global-shell-pvm: that proves five cross-chart saturation deficits are sufficient to authenticate the shell; this proves the first such deficit is not controlled by the fixed shell covariance Laplacian or lattice root relations.
  sl3-one-parahoric-multiplicity-flow-has-a-tracezero-gauge: that uses a continuous unitary spectator in one edge transport; this uses two full 42-atom systems of imprimitivity and computes their exact cross-Gram deficit as 41/42.
  six-parahoric-finite-fiber-folds-remain-amenable: that is a large-scale Folner construction over the coweight lattice; this is a fixed finite-dimensional two-chart obstruction already in the kernel of the complete 42-point actor Laplacian.
---

Let

```text
C=SL_3(Z),       D=C cap hCh^(-1),       Omega=C/D,
|Omega|=42.
```

Identify any two Weyl parahoric charts with `Omega` by the canonical
bijections of `five-parahoric-overlap-saturations-give-global-shell-pvm`.
On

```text
H=l^2(Omega times Omega)
```

let `C` act diagonally:

```text
rho(g) delta_(x,y)=delta_(gx,gy).                       (TSE1)
```

Define two complete shell PVMs by the coordinate projections

```text
P_i delta_(x,y)=1_(x=i) delta_(x,y),
Q_i delta_(x,y)=1_(y=i) delta_(x,y).                    (TSE2)
```

Both systems are exactly covariant under the SAME actor representation:

```text
rho(g)P_i rho(g)^*=P_(gi),
rho(g)Q_i rho(g)^*=Q_(gi).                              (TSE3)
```

Hence every finite-shell intertwiner Laplacian, every root/Weyl relation in
`C`, and every chart-internal first-exit term vanishes exactly.  This
includes all Steinberg and mixed-root words which stay inside the lattice
actor.

Nevertheless, with normalized trace on `M_(42^2)`,

```text
tr(P_i)=tr(Q_i)=1/42,
tr(P_iQ_i)=1/42^2,                                     (TSE4)
```

so the adjacent-chart authentication deficit is

```text
Delta=(1/2) sum_i ||P_i-Q_i||_2^2
     =sum_i (1/42-1/42^2)
     =41/42.                                            (TSE5)
```

Thus no estimate

```text
Delta <= C (shell covariance energy
             + lattice mixed-root energy
             + chart-internal first-exit mass)          (TSE6)
```

can hold, for any finite `C`.

The countermodel survives canonical-character normalization.  Tensor
`(TSE1)--(TSE2)` with the left regular representation of
`G_a=SL_3(Z/p^a Z)`, letting the PVMs act only on the two-coordinate factor.
For every fixed finite set of nonidentity lattice words, all normalized
traces are exactly zero once `a` is large enough, while `(TSE3)--(TSE5)` are
unchanged.  The blocks may therefore be taken arbitrarily deep in the
denominator-primary congruence tower.

Representation-theoretically, the finite shell Laplacian projects onto the
whole commutant of the diagonal action on `Omega times Omega`; the diagonal
matching is only one orbital sector.  Conditional expectation onto its
kernel cannot select that sector without one extra incidence observable.
The missing term must involve the denominator generator (or an equivalent
raw same-vertex return) and distinguish the diagonal orbit `x=y` from the
off-diagonal orbitals.  A projective trace-square identity involving only
the lattice actor cannot do this, because the actor representation above is
exact.

This is not a representation of `SL_3(Z[1/p])`: exact finite-dimensional
extension is precisely what co-density forbids.  It proves that the desired
simple-neighbor inequality must consume a denominator relation coupling the
two coordinate systems, not merely the fixed 42-point spectral gap.  It
also does not touch the uniformly noncorrectable lattice-microstate sector;
all shell-decoding statements remain conditional on a correctable vertex
until a separate canonical correction theorem is supplied.
