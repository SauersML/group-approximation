---
rg: 2
id: stw83-compressed-one-colour-carries-circle-matrix-finite-sets
kind: claim
title: One moving matrix colour carries every circle-coefficient finite set after plateau compression
distinct_from:
  stw83-rotating-order-zero-compression-escapes-circle-gap: that treats the circle generator in a rank-one compression; this gives a simultaneous completely positive factorization for arbitrary finite subsets of every matrix-over-circle corner and preserves constant matrix data exactly.
  stw83-plateau-buffer-recolouring-hinge: that asks for an uncompressed two-colour approximation compatible with the Toeplitz transition and tail; this proves the coefficient finite set itself can be carried by one crossing colour but leaves its off-plateau leakage uncontrolled.
---

**ESTABLISHED.**  Fix `k>=1`, a finite set
`Omega subset M_k(C(T))`, and `epsilon>0`.  There are points
`t_1,...,t_m in T`, the finite-dimensional algebra

```text
F=direct-sum_(j=1)^m M_k,
```

a unital star homomorphism

```text
phi:M_k(C(T))->F,       phi(x)=(x(t_1),...,x(t_m)),
```

a unital star homomorphism

```text
psi:F->M_(mk)(C(T)),
```

and a constant rank-`k` projection `p in M_(mk)(C(T))` such that, after
identifying `pM_(mk)(C(T))p` with `M_k(C(T))`,

```text
norm(p psi(phi(x)) p-x)<epsilon      for every x in Omega.       (1)
```

Moreover, under the tensor identification
`M_(mk)=M_m tensor M_k`, the construction satisfies

```text
psi(phi(1 tensor a))=1_m tensor a        for every a in M_k.     (2)
```

Thus arbitrary finite coefficient data, not merely the coordinate unitary,
can be encoded simultaneously on a plateau diagonal by one
star-homomorphic, hence order-zero, colour whose range genuinely crosses the
plateau boundary.  There is no residual topological or complete-positivity
obstruction at the compressed-return level.

This does not prove `dim_nuc(A_N)=1`.  The uncompressed return
`psi phi(x)` has additional matrix blocks outside `p`; compression is
not an order-zero operation in general, and in the nontrivial moving-frame
cases it does not preserve order zero.  The exact remaining task is
therefore to absorb or align this off-plateau leakage with the scalar
Toeplitz buffer while preserving the two global orthogonality pairings in
[[stw83-plateau-buffer-recolouring-hinge]].

DERIVATION
[[stw83-compressed-matrix-finite-set-carrier-proof]]
