---
rg: 2
id: modular-vertex-noncongruence-proof
kind: route
title: Restrict generic infinite-image representations of the modular free product
target: modular-vertex-extension-does-not-force-congruence
requires:
  - residual-finite-tensor-camouflages-iwahori-transfer-failures
---

Kill the central involution and use

```text
PSL_2(Z) ~= C_2 * C_3.                                  (MVP1)
```

This free product has irreducible unitary representations of arbitrarily
large finite dimension and infinite image.  One direct construction is to
choose an involution `S` and an order-three unitary `R` with prescribed
nontrivial spectral multiplicities in generic relative position.  The
common commutant of their spectral projections is then scalar, so the
representation is irreducible.  The locus where an additional nontrivial
word in `S,R` equals the identity is a proper real-algebraic subset for
each word.  Avoiding their countable union makes the image of
`C_2*C_3` infinite.  Lifting along `SL_2(Z)->PSL_2(Z)` gives the required
`pi_n`.

Let `theta` be any irreducible constituent of `pi_n|B`.  Frobenius
reciprocity gives a nonzero map

```text
pi_n -> Ind_B^C(theta).
```

Irreducibility makes it injective, and `[C:B]=3`, hence

```text
dim(pi_n) <= 3 dim(theta).                              (MVP2)
```

If every constituent of `pi_n|B` had finite image, the finite direct sum
`pi_n(B)` would be finite.  Since `B` has finite index in `C`, `pi_n(C)`
would then be a union of finitely many cosets of a finite group and hence
finite, a contradiction.  At least one constituent has infinite image;
`(MVP2)` gives `(MVC1)` for it.

The last paragraph of the claim follows from the exact tensor calculation
in `residual-finite-tensor-camouflages-iwahori-transfer-failures`: regular
trace can be imposed without changing the edge defect or a tensor-stable
outlier witness.  No congruence projection is produced by that operation.
