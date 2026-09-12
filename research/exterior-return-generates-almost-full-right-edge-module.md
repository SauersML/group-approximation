---
rg: 2
id: exterior-return-generates-almost-full-right-edge-module
kind: claim
title: A vanished exterior return generates an asymptotically full right edge module
distinct_from:
  kt-extrinsic-corrector-is-an-orthogonal-index-one-correspondence: That constructs an exact index-one correspondence from a unitary corrector in an infinite tracial model; this extracts an almost index-one right module directly inside each finite matrix coordinate from one approximate exterior return.
  commutant-density-trace-blind: That computes the normalized dimension of the full actor commutant in the adjoint space; this computes Murray--von Neumann dimension over the edge algebra of one cyclic off-edge module.
---

Retain the finite-matrix notation

```text
x=T^*phi(gamma)T,          z=E_B(x),
y=x-z,                    ||z||_2<=q+eta.              (ARM1)
```

Let `r=1-supp(|y|)` be the right kernel projection of `y`.  Then

```text
tr(r)<=||z||_2^2<=(q+eta)^2,                           (ARM2)
```

and hence

```text
tr(supp(|y|))>=1-(q+eta)^2.                            (ARM3)
```

The cyclic space `yB` lies in `L2(B)^perp` because the conditional
expectation is right `B`-modular.  If

```text
I_y={b in B:yb=0}=eB
```

for its unique kernel projection `e in B`, then

```text
dim_B(overline(yB))=tr(1-e)>=1-(q+eta)^2.              (ARM4)
```

Thus a vanished exterior return does more than force a quarter-trace carrier:
it inserts an asymptotically full copy of the standard right `B`-module into
the orthogonal complement of `L2(B)`, with a padding-stable module dimension.

This still does not authenticate a positive-density **adjoint** carrier.
`full-right-edge-module-can-have-vanishing-adjoint-density` gives exact
canonical-character Kazhdan blocks where `dim_B(yB)=1` but

```text
dim_C(yB)/dim_C(L2(M_d))->0.                            (ARM5)
```

The remaining conversion must therefore use more than right-module dimension:
it must couple this index-one module to a left action, a common physical
reducing projection, or the strict full-actor transport.

DERIVATION
exterior-return-right-module-dimension-proof
