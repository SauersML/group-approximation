---
rg: 2
id: rf-reynolds-mask-deficit-is-not-relator-energy
kind: claim
title: Residual finiteness gives zero-energy models with every canonical Reynolds mask deficit
distinct_from:
  residually-finite-models-refute-filtered-wandering-return: that treats one filtered off-diagonal moment `tau(Pr)`; this treats an arbitrary positive weighted sum of finite-support projection codimensions and permits finite canonical trace constraints in the alleged energy.
  embedded-packet-projection-has-no-relator-ideal-certificate: that refutes a trace-universal inequality by the infinite left regular representation; this produces exact finite-dimensional countermodels, so it rules out inequalities asserted only for matrices.
  finite-edge-hnn-closures-cannot-finish-the-nonce-atlas: that excludes completion of one no-CE atlas by residual-finiteness permanence; this gives the explicit dimension-free mask-versus-relator-energy obstruction for every residually finite Hecke/Reynolds row system.
---

**ESTABLISHED.**  Let `Gamma=<S|R>` be residually finite.  Let
`q_1,...,q_m` be finite-support projections in `C[Gamma]`, let `omega_j>0`,
and put

```text
D_Gamma=sum_j omega_j tau_Gamma(1-q_j).                (RME1)
```

If `D_Gamma>0`, there is no finite set of presentation relators `R_0`, no
finite constant `C`, and no dimension-uniform inequality

```text
sum_j omega_j tr_d(1-q_j(U))
 <=C sum_(r in R_0)||r(U)-I||_(2,d)^2                 (RME2)
```

valid for all exact finite-dimensional representations (and hence none valid
for all approximate representations on which the evaluated `q_j` have been
rounded to projections).

The obstruction survives finitely many canonical trace tests.  Given a
finite word window `W subset Gamma minus {1}`, there is one finite quotient
regular representation `rho` such that

```text
rho(r)=I                              (r in R),
tr(rho(w))=0                          (w in W),
sum_j omega_j tr(1-rho(q_j))=D_Gamma.                 (RME3)
```

Thus adding finitely many penalties `|tr(w(U))|^2` to the right side of
`(RME2)` still leaves an exact zero-energy countermodel.

## Explicit Reynolds and character masks

If `H<=Gamma` is finite and `chi` is an irreducible character, let

```text
z_chi=(dim chi/|H|)sum_(h in H)chi(h^(-1))h.           (RME4)
```

For the high-density mask `q=1-z_chi`,

```text
tau_Gamma(1-q)=(dim chi)^2/|H|.                        (RME5)
```

This includes nontrivial character masks, for which the augmentation of `q`
is one and the trivial representation sees no deficit.  Nevertheless a
finite quotient injective on `H` restricts in its regular representation to
copies of the regular `H`-representation and sees exactly `(RME5)`.  Hence
switching from the trivial Reynolds atom to an augmentation-safe nontrivial
Fourier atom does not produce relator-energy payment in a residually finite
row system.

For the trivial Reynolds projection `e_H`, the complementary mask
`q=1-e_H` is ruled out even by the trivial representation: its augmentation
is zero and its deficit there is one.  Formula `(RME5)` is the sharper
firewall that also handles all nontrivial character choices.

## Necessary escape

For an arbitrary finitely presented group, any inequality `(RME2)` forces
every deleted projection `1-q_j` with positive weight to vanish in every
exact finite-dimensional representation: set the relator defect to zero and
use positivity.  Therefore a row-energy compiler with positive canonical
deficit must place its deleted mask projections in the finite-dimensional
representation radical while leaving them nonzero in `C[Gamma]`.  A robust
version of `(RME2)` is stronger still: it must put their canonical mass in a
normalized-HS approximation radical.

This is compatible with an exact infinite tracial BCS model, where the
deleted projections may vanish.  It proves that finite subgroup
Reynolds/Hecke rows, finite amalgams, and finite-subgroup HNN covariance do
not create the required payment while the resulting system remains
residually finite.  The missing ingredient must be a non-Bass--Serre relation
among the intertwiners (or an infinite actor) that creates precisely this
finite-dimensional radical.  Constructing its dimension-uniform HS modulus
is already the substantive groupification problem, not another Reynolds
rank estimate.

DERIVATION
rf-reynolds-mask-energy-countermodel-proof
