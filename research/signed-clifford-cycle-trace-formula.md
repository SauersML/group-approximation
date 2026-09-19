---
rg: 2
id: signed-clifford-cycle-trace-formula
kind: claim
title: Signed Clifford cycle parity exactly determines the implementing trace
distinct_from:
  marked-clifford-compressor-hyperfinite-invisibility: that uses trace zero to obstruct hyperfinite marked representations; this computes the exact trace, including every nonzero case, for an arbitrary signed permutation of a finite Clifford block.
  marked-clifford-table-exponential-dimension: that extracts a dimension lower bound from an all-pairs approximate Clifford table; this is an exact character formula for one normalizing signed permutation.
---

Let `c_1,...,c_(2m)` be the standard self-adjoint anticommuting generators
of the complex Clifford algebra

```text
C=Cl_(2m)(C) isomorphic to M_(2^m).
```

Let `R` be a signed permutation of their real linear span,

```text
R(c_i)=epsilon_i c_(pi(i)),             epsilon_i in {+1,-1},
```

and let `V in U(C)` implement the induced automorphism.  For a cycle `D` of
`pi`, put

```text
s_D=product_(i in D) epsilon_i,
```

and let `r` be the number of cycles of `pi`.  Then

```text
|tr_(2^m)(V)|^2
 =2^(-2m) det(1+R)
 =2^(-2m) product_D (1-(-1)^(|D|) s_D).                (SCT1)
```

Consequently the normalized trace of `V` is zero exactly when at least one
cycle satisfies

```text
s_D=(-1)^(|D|).                                         (SCT2)
```

If no cycle satisfies `(SCT2)`, then every factor in `(SCT1)` is `2` and

```text
|tr_(2^m)(V)|=2^(r/2-m).                                (SCT3)
```

Thus an unsigned even cycle or a signed odd cycle with negative sign-product
already forces trace zero.  A fixed-point-free unsigned involution is only
the special case in which every cycle is a transposition.
