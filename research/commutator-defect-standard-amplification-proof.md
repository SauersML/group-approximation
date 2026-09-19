---
rg: 2
id: commutator-defect-standard-amplification-proof
kind: route
title: Count fixed tuples of an amplified commutator
target: commutator-defect-survives-standard-amplification
requires:
  - commuting-sofic-actions-need-not-combine
---

Let `r=[p,q]`.  The normalized Hamming defect is

```text
delta=1-|Fix_A(r)|/|A|.
```

## Coordinatewise powers

The commutator of coordinatewise permutations is coordinatewise:

```text
[p^[k],q^[k]]=r^[k].
```

A tuple in `A^k` is fixed by `r^[k]` exactly when each of its
coordinates is fixed by `r`.  Hence

```text
|Fix_{A^k}(r^[k])|/|A|^k
 =(|Fix_A(r)|/|A|)^k
 =(1-delta)^k.
```

Taking the complement proves

```text
d_Ham([p^[k],q^[k]],1)=1-(1-delta)^k.
```

Since `0<=1-delta<=1`, one has
`(1-delta)^k<=1-delta`, which gives the lower bound in `(CAS1)`.
Thus configuration powers worsen every nonzero defect unless `k=1`.

The same count works for nonidentical factors.  If pairs
`(p_i,q_i)` on `A_i` have defects `delta_i`, their product pair
has commutator defect

```text
1-product_i(1-delta_i).                                 (CAP1)
```

In particular, adjoining any exactly commuting factor, for which
`delta_i=0`, leaves the original defect unchanged.

## Disjoint unions

On a disjoint union of `k` equal copies, the commutator restricts to
`r` on each component.  Both the number of moved points and the total
number of points are multiplied by `k`, so their ratio remains
`delta`.  For unequal components the new defect is only a weighted
average of the component defects; repeating a bad component cannot drive
its defect down.

Therefore the standard size-amplification operations used to improve
sampling or freeness cannot manufacture the cross-commutation relations
for `F_m x F_m`.  Small commutator defect must already be present in
the joint finite model.
