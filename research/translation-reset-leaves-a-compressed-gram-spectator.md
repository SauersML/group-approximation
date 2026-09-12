---
rg: 2
id: translation-reset-leaves-a-compressed-gram-spectator
kind: claim
title: The translation reset leaves a sharp compressed-Gram spectator on its scalar multiplicity ray
artifacts:
  - research/artifacts/translation-reset-compressed-gram-spectator-2026-08-21.md
distinct_from:
  two-fixed-packet-reynolds-actions-leave-a-gram-spectator: that inserts an arbitrary spectator projection fixed by bounded packet Reynolds maps; this realizes the spectator exactly as the deficiency of the native one-sided compression and saturates the guarded rank floor.
  symmetrized-reset-collapses-schur-flow-to-one-ray: that removes every transverse finite packet type and leaves one scalar amplification parameter; this shows that the surviving scalar parameter is already large enough to carry the whole compressed-Gram defect.
  diagonal-difference-shift-propagates-pauli-incidence: that forces the chord and shifted selectors to commute with all addressed old-spin Paulis; this gives an exact model of those incidences whose Gram still lies in the label--residual algebra rather than the finite label algebra.
---

Let `rho:Rhat_f->U(V)` be one exact negative-central-character label
representation of the translation-symmetrized full reset.  Let
`H_0<=E_0` be its guarded packet projections, and write

```text
d=dim(V),       r=rank(E_0),       s=rank(H_0),
0<s<r,          F_0=E_0-H_0.                              (RGS1)
```

For the native guarded packet, `s/d=1/8`.  Choose `N` with `r` dividing
`sN`, and choose a nontrivial projection `Q in M_N(C)` of rank `sN/r`.
On `V tensor C^N` put

```text
E=E_0 tensor I_N,       H=H_0 tensor I_N,
F=E-H,                  q=E_0 tensor Q.                  (RGS2)
```

Then `rank(E-q)=rank(F)`.  Hence there is a unitary `U` carrying
`(E-q)(V tensor C^N)` onto `F(V tensor C^N)` and its orthogonal complement
onto `F^perp`.  It may be chosen to be a symmetry.  For

```text
X=FUE                                                       (RGS3)
```

one has exactly

```text
X^*X=E-q,
||X^*X-E||_2^2=tr(q)=s/d=tr(H)=1/8.                       (RGS4)
```

Thus this model sharply saturates
`fanizza-compressed-unitary-has-guarded-rank-floor`.

All translation-reset and local type-vector constraints remain exact under
the amplification `rho tensor I_N`.  Nevertheless `q=E_0 tensor Q` is not
in the finite label algebra `rho(C[Rhat_f]) tensor I_N` when `Q` is
non-scalar.  It lies in the label--residual algebra and uses precisely the
sole scalar multiplicity ray left by
`symmetrized-reset-collapses-schur-flow-to-one-ray`.

The coordinate-Pauli and diagonal-difference incidences do not remove the
model.  Tensor with an old-spin Toeplitz representation, put every addressed
Pauli in that factor, and put `E,H,U` in `V tensor C^N`.  With

```text
t=T tensor U,       U_chord=I tensor U,       c=t U_chord^(-1)=T tensor I,
                                                               (RGS5)
```

all relations of
`diagonal-difference-shift-propagates-pauli-incidence` hold exactly, and
the Pauli conditional expectation merely returns the already localized
operator `q`.

Consequently the semisimple gap `gamma_A` cannot be applied: its hypothesis
is membership in the finite label algebra, not merely in
`label tensor residual` or in the old-spin commutant.  The reset fixes the
label type vector but imposes no mixed condition on the chord's scalar
multiplicity coordinate.  A successful source-fullness decoder must add a
genuinely mixed chord--reset relation whose value changes under the
replacement of a label projection by `E_0 tensor Q`; local reset tables,
their Reynolds constraints, and coordinate-Pauli localization do not force
that relation.
