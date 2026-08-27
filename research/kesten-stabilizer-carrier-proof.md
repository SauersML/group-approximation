---
rg: 2
id: kesten-stabilizer-carrier-proof
kind: route
title: Free the nonedge commutators and take a stabilizer-invariant Kesten quantile
target: stabilizer-orbit-commutators-have-a-kesten-chart-carrier
requires:
  - nonedge-spectrum-cannot-descend-to-forty-two-chart
  - native-sl3-group-is-hecke-graph-wreath-product
  - native-forty-two-shell-has-a-noncommuting-pair
---

The orbit in `(KCC2)` is finite because

```text
Stab_D(y)=D cap h^(-1) C h
```

has finite index in `D`; all three groups are commensurable arithmetic
lattices. The element `x_21(1)` from `(KSD3)` proves the orbit is nontrivial.

Let `B_O` be the graph product on the lamps `(c_z)_(z in O)`. Since `x` is
nonadjacent to every point of `O`, the induced graph-product subgroup is

```text
<c_x> * B_O = C_2 * B_O.                                (KCP1)
```

Expand a freely reduced word in formal letters `kappa_z^(+-1)` using

```text
kappa_z=c_x c_z c_x c_z,
kappa_z^(-1)=c_z c_x c_z c_x.                           (KCP2)
```

Free-product reduction cannot erase it. The only possible boundary
cancellation is between a negative letter and a positive letter; after the
two adjacent `c_x` syllables cancel, the neighboring `B_O` syllable is
`c_zc_w`, which is nonidentity unless the two formal letters were inverse,
excluded by free reduction. This proves `(KCC4)`.

Conjugation by `D` fixes `x` and permutes `O`, hence permutes the free basis
in `(KCC4)` and fixes `S`. In the canonical trace, `S` is the adjacency
operator of the `2m`-regular tree. Its Kesten distribution is atomless; its
cumulative distribution therefore has a `1/42` quantile, proving `(KCC6)`.

Stabilizer invariance makes `(KCC7)` independent of coset representatives.
Finally expand

```text
||sum_iE_i-I||_2^2
 =sum_i tau(E_i)+sum_(i!=j)tau(E_iE_j)
  -2sum_i tau(E_i)+1,
```

and use `sum_i tau(E_i)=42/42=1` to obtain `(KCC8)`.
