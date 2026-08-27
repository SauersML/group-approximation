---
rg: 2
id: external-weyl-tightening-is-only-column-weighting
kind: claim
title: External Weyl or ETF tightening is only column weighting
distinct_from:
  affine-frobenius-tight-defect-column-frame: that asks for a correlated internal packet construction; this rules out the proposed universal frame when it acts only in an external matrix coordinate.
  algebraic-selector-mixing-frame-collapses-forbidden-sector: that treats an internally mixing selector frame and its predicate consequence; this is a direct tensor-factor calculation requiring no selector semantics.
---

**ESTABLISHED.**  Let `r_i` be projections in a finite tracial algebra and,
for each `i`, let `(f_(i,a))_a` be projections in an external matrix factor
satisfying

```text
sum_a f_(i,a)=c_i I.                                   (EWT1)
```

This includes a complete finite Weyl orbit or any tight equiangular
projection frame in the external coordinate.  Replace the `i`th defect
projection by the family

```text
R_(i,a)=r_i tensor f_(i,a).                            (EWT2)
```

Then

```text
sum_(i,a) R_(i,a)=(sum_i c_i r_i) tensor I.            (EWT3)
```

Therefore the enlarged family is tight on its join if and only if the
original internal projections are already a weighted tight fusion frame
with weights `c_i`.  An external Weyl orbit, ETF, column register, or
block-diagonal stabilization cannot flatten the internal singular-value
spectrum.  It only implements scalar column weights.
