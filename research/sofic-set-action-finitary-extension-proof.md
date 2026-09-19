---
rg: 2
id: sofic-set-action-finitary-extension-proof
kind: route
title: Transport finite permutations through the orbit charts and amplify
target: sofic-set-action-finitary-extension-is-sofic
requires:
  - gkp-sofic-action-toolkit
---

Put `D=Sym_fin(Y)`.  Fix a finite multiplication and separation window
`Omega subset D rtimes H` and `epsilon>0`.  Enlarge the finite actor window
`F subset H` and the finite family `P subset D` so that all factors,
products, inverses and conjugates queried by `Omega` occur in them.  There is
a finite `E subset Y` which contains the supports of all permutations in
`P`, their images, and every translate needed by the conjugation checks.
Every `p in P` restricts to a permutation of `E` and is the identity off
`E`.

Choose a GKP `(F,E,delta)` orbit approximation.  Thus there are a finite
actor-state set `A`, a map `phi:H->Sym(A)`, a subset
`S subset A` of relative size greater than `1-delta`, a finite label set
`B`, and injections

```text
pi_s:E->B                    (s in S)
```

which satisfy the orbit-covariance equation whenever all queried terms stay
in the good window.  For `p in P` and `s in S`, transport `p|E` through
`pi_s` and extend it by the identity on `B\pi_s(E)`; call the resulting
permutation `p_s in Sym(B)`.  On bad fibres put `p_s=1`.  Define

```text
D_A(p)(s,b)=(s,p_s(b)),
T_A(h)(s,b)=(phi(h)s,b)                         (s in A, b in B).
```

On every fibre for which `s`, `phi(h)s`, and the relevant orbit-chart terms
are good, the orbit-covariance equation gives

```text
T_A(h) D_A(p) T_A(h)^(-1) = D_A(h p h^(-1)).   (FSP1)
```

The failure set has relative size `O_Omega(delta)`.  Multiplication inside
the `D` coordinate is exact on good fibres because each `pi_s` is injective,
and multiplication of the `T_A(h)` has the defect of `phi`.  Hence

```text
(p,h) |-> D_A(p)T_A(h)
```

is an `O_Omega(delta)`-multiplicative map to `Sym(A x B)`.

The definition of a sofic set action does not require `phi` itself to
separate actor elements.  Use, in parallel, an ordinary sofic approximation
of the sofic group `H`, taking a Cartesian product of the two permutation
models.  Actor elements in the finite window are then separated.  If the
actor coordinates agree but `p!=q`, injectivity of every good `pi_s` shows
that `D_A(p)` and `D_A(q)` differ on at least one label in each good fibre.
Thus their normalized Hamming distance is at least

```text
(1-delta)/|B|.                                  (FSP2)
```

This is positive but need not be close to one.  Take a fixed Cartesian power
of the whole model.  If two permutations agree on a fraction at most
`1-c`, their diagonal Cartesian powers agree on a fraction at most
`(1-c)^m`; choose `m` so this is below `epsilon`.  The multiplication defect
of the Cartesian power is at most `m` times the original defect, so first
choose `m` and then choose `delta` sufficiently small.  All distinct elements
of `Omega` are now `1-epsilon` separated and all products in `Omega` are
`epsilon` accurate.  This is a sofic approximation of `D rtimes H`.

Finally, every sofic group is hyperlinear, so its group von Neumann algebra
is Connes embeddable.
