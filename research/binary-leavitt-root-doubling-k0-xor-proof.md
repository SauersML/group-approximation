---
rg: 2
id: binary-leavitt-root-doubling-k0-xor-proof
kind: route
title: Expand the negative cut of a product of commuting involutions
target: binary-leavitt-root-doubling-k0-retains-xor-overlap
requires:
  - matrix-corona-projection-monoid-is-rank-germs
---

Because `p_0,p_1` commute, the four Boolean atoms

```text
p_0p_1,  p_0(1-p_1),  (1-p_0)p_1,  (1-p_0)(1-p_1)
```

are pairwise orthogonal.  Substitution of `u_i=1-2p_i` gives

```text
(1-u_0u_1)/2=p_0+p_1-2p_0p_1
              =p_0(1-p_1)+(1-p_0)p_1.
```

The decompositions

```text
p_0=p_0p_1 direct-sum p_0(1-p_1),
p_1=p_0p_1 direct-sum (1-p_0)p_1
```

give `(KXO3)` in the Grothendieck group.  If the three large projections
have common class `b` and the overlap has class `c`, cancellation gives
`b=2b-2c`, hence `b=2c`.  There is no equation `b=2b`.

For the concrete model take

```text
p_0=diag(1,1,0,0),             p_1=diag(0,1,1,0).
```

Their intersection has rank one and their XOR has support on coordinates
one and three, hence rank two.  Put `u_i=1-2p_i` and take constant sequences
in the matrix corona

```text
prod_n M_4(C) / direct-sum_n M_4(C).
```

Rank-two projections in `M_4(C)` are unitarily conjugate, so all three
classes agree and remain nonzero in the corona.  Rank-germ classification
confirms directly that the common dimension germ is the constant sequence
two while the overlap germ is the constant sequence one.

