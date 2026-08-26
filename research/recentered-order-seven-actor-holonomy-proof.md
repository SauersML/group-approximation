---
rg: 2
id: recentered-order-seven-actor-holonomy-proof
kind: route
title: Close the recentered hub pairs and tensor the Singer actor group by its regular representation
target: recentered-order-seven-heads-have-actor-holonomy
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
  - middle-index-order-seven-orbit-cut-is-native-scale-neutral
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
---

For `k in K={4,5,7,8,9}` put

```text
r_4=r_5=s_4=s_5=q,
r_7=a_1, r_8=a_2, r_9=a_3,
s_7=b_1, s_8=b_2, s_9=b_3,
X_k=x_(18,k)(r_k),       Y_k=x_(k,19)(s_k).           (ROHP1)
```

Prefix cancellation gives `r_ks_k=q`.  Different middle indices are
noncomposable, while equal indices give `x_(18,19)(q)=C`.  This proves the
five-pair Pauli table.

As in the native center-chain calculation, write

```text
E_(k,l)=x_(k,l)(s_kr_l).
```

Conjugation gives

```text
E_(k,l): X_k |-> X_kX_l,       Y_l |-> Y_lY_k,        (ROHP2)
```

and fixes the remaining named generators.  Here

```text
A_1=E_(4,7),       B_2=E_(8,4),
A_2=E_(5,8),       B_3=E_(9,5).                       (ROHP3)
```

Applying `(ROHP2)` first to `A_1`, then to `B_2`, proves `(ROH5)`.
The literal Whitehead swaps pairs `7,8`, proving `(ROH6)`; the second row is
identical.  The matrix in `(ROH6)` is the Singer matrix already computed in
the native order-seven proof, so its seventh power is one.

Since the Pauli representation on a fixed central `-1` block is irreducible,
two implementers of one actor action differ by a unitary in its multiplicity
commutant.  This proves `(ROH7)`.  Multiplication and the canonical label
identity `(S_iL_i)^7=1` give `(ROH8)`.

For the finite fence, the transformations `(ROHP2)` and the two swaps
generate a finite matrix group `G<=GL_5(F_2)`.  The Schrodinger Pauli
representation and its canonical linear-change implementers give a
representation of the semidirect product.  Tensoring the implementer of
every `g` with `lambda(g)` preserves every multiplication and covariance
relation.  In particular the gauge of a product is the corresponding
regular operator:

```text
(U_(J_i) tensor lambda(J_i))(U_(v_i) tensor lambda(v_i))
 =U_(T_i) tensor lambda(T_i).                          (ROHP4)
```

The exact relation `T_i^7=1` proves its seventh power is one.  Since `J_i`
is a nonidentity involution in `G`, left translation by `J_i` has a
`-1` eigenspace, so `||lambda(J_i)-I||=2`.  This proves the fence.
