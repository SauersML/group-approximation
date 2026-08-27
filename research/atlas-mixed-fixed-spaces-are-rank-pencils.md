---
rg: 2
id: atlas-mixed-fixed-spaces-are-rank-pencils
kind: claim
title: Atlas mixed fixed-space charges are rectangular rank pencils, not finite lifting data
distinct_from:
  atlas-separate-chart-module-ledger-is-kernel-blind: that identifies mixed intersections as the first surviving candidates and proves their abstract rank-Lipschitz property; this gives their exact matrix-pencil form, their ultraproduct interpretation, and the obstruction to using them as a finite-coordinate compactness argument.
  atlas-augmented-rank-zero-set-compactness: that asks for an exact finite zero of the entire augmented Laurent system; this proves that finitely many mixed fixed-space values do not themselves perform such a lift.
---

Let `E_n` be a finite-dimensional vector space, let two fixed finite groups
`K,L` act on it through the two repeated Atlas charts, and choose generating
lists `k_1,...,k_r` and `l_1,...,l_s`.  Define the rectangular operators

```text
A_K=column(k_1-I,...,k_r-I),
A_L=column(l_1-I,...,l_s-I).
```

For every relative gauge `T in GL(E_n)`, the mixed coordinate is exactly

```text
mu_(K,L)(T)
 =dim(Fix_K(E_n) intersect T^-1 Fix_L(E_n))
 =dim ker column(A_K,A_L T)
 =dim(E_n)-rank column(A_K,A_L T).                    (MFP1)
```

Consequently every finite list of the proposed mixed charges is only a
finite list of normalized ranks of degree-one rectangular matrix pencils in
`T`.  In particular, for a rank-metric ultraproduct point `[T_n]`,

```text
lim_U mu_(K,L)(T_n)/dim(E_n)
 =1-rk_U(column(A_K,A_L[T_n])).                       (MFP2)
```

Thus the charge passes to the ultraproduct exactly; it does not select a
coordinate on which the augmented relations vanish exactly.  A proof of
`atlas-augmented-rank-zero-set-compactness` cannot use a recurring finite
mixed-intersection profile, because these profiles are not a finite
alphabet.  Already for `E=F2^(2m)` and two coordinate `m`-planes `F=G`, an
invertible `T` can realize

```text
dim(F intersect T^-1 G)=j
```

for every `0<=j<=m`.  After normalization these values become dense in
`[0,1/2]` as `m` grows.

The precise surviving uses of `(MFP1)` are therefore:

1. prove a universal Sylvester-rank inequality from the augmented relations
   which already contradicts the faithful-chart rank inside the rank
   ultraproduct; or
2. combine a mixed-coordinate separation of exact strata with a relative
   rank-correction theorem which moves an approximate augmented point to one
   of those exact strata while preserving the packet.

The second item is the missing amalgam/filling rank-stability operation
fenced by `atlas-rank-stability-literature-fence`.  Merely taking limits of
the numbers in `(MFP2)` supplies neither operation.

