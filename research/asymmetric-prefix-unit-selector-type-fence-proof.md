---
rg: 2
id: asymmetric-prefix-unit-selector-type-fence-proof
kind: route
title: Compare the Pauli label ranks under the asymmetric prefix conjugacy
target: asymmetric-prefix-unit-cannot-conjugate-unequal-selector-types
requires:
  - asymmetric-prefix-unit-conjugates-native-whiteheads
  - asymmetric-prefix-unit-misses-fixed-hecke-frame
  - quarter-whiteheads-lack-unequal-source-conjugacy
  - center-chain-four-hecke-flags-have-native-ranks
---

The exact prefix-code calculation gives only

```text
Ad_G(J_1)=J_2.                                         (1)
```

In the common three-qubit label model, `J_1` and `J_2` are adjacent swaps.
An adjacent swap of two qubits has a two-dimensional negative eigenspace in
dimension eight, so both label negative fractions are `2/8=1/4`.  Thus
`(1)` preserves the raw label type.

Suppose that `(1)` extended to the complete typed Pauli packets.  On their
label algebras it would induce a unital star-isomorphism

```text
alpha:M_8(C) -> M_8(C).                                (2)
```

Every such map is inner.  More elementarily, it preserves the normalized
matrix trace because that trace is the unique normalized tracial state on
`M_8(C)`.  Therefore

```text
tr_8(alpha(P))=tr_8(P)                                 (3)
```

for every label projection `P`.  The target label projections required by
the two selector rows have ranks two and one, respectively.  Equation `(3)`
forbids mapping the rank-two quarter projection to the rank-one eighth
projection.  The source projections have ranks four and two, so the same
argument forbids their proposed conjugacy.

For the quantitative statement, if `P,Q` are projections of normalized
ranks `p,q`, then

```text
||P-Q||_2^2
=p+q-2tr(PQ)
>=p+q-2 min(p,q)
=|p-q|.                                                (4)
```

For the associated reflections `C_P=1-2P` and `C_Q=1-2Q`,

```text
||C_P-C_Q||_2^2=4||P-Q||_2^2>=4|p-q|.                 (5)
```

Substituting `(p,q)=(1/4,1/8)` and `(1/2,1/4)` gives
`(ASC4)`.

Finally, an isomorphism between two irreducible Pauli packets has an inner
label implementer.  Dividing a full implementer by that label unitary
leaves an operator in the commutant `1 tensor B(M)`.  Hence every full
packet implementer factors as `W_label tensor V_res`.  The reservoir factor
cannot alter `(3)`.  Multiplying one simple tensor factor by `-1` replaces
the label negative fraction by its complement only, and does not turn
`1/4` into `1/8`.  Conjugating the whole carrier from `F` to `F'` preserves
both its dimension and every relative spectral rank.  This proves the
scoped fence.
