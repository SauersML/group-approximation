---
rg: 2
id: elementary-root-kernel-equals-level-proof
kind: route
title: Conjugate one root kernel to every other root using elementary signed permutations
target: elementary-root-kernel-equals-level
requires: []
---

The matrix

```text
w_ij=e_ij(1)e_ji(-1)e_ij(1)
```

has block `[[0,1],[-1,0]]` on coordinates `i,j`. These matrices generate
signed coordinate permutations whose underlying permutations are all of
`Sym(n)`. Their entries `1,-1` are central over every unital ring.

Given ordered distinct pairs `(i,j)` and `(k,l)`, choose such a signed
permutation `w` carrying the first pair to the second. Matrix
multiplication gives

```text
w e_ij(a) w^-1=e_kl(epsilon*a),    epsilon in {1,-1}.
```

Normality carries membership in `N` across this conjugation. Taking
inverses removes the sign because `e_kl(-a)=e_kl(a)^-1`. Thus membership
for one root is equivalent to membership for every root, proving that its
kernel is `I`.

The map `a -> e_ij(a)N` is an additive homomorphism with that kernel, so
the first isomorphism theorem identifies its image with `(U/I,+)`.
The usual Steinberg commutators also show that `I` is a two-sided ideal:
for distinct indices, `[e_ki(b),e_ij(a)]=e_kj(ba)` and
`[e_ij(a),e_jk(b)]=e_ik(ab)`. Normality and the preceding equality of root
kernels imply closure under left and right multiplication. QED
