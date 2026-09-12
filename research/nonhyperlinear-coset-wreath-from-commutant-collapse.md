---
rg: 2
id: nonhyperlinear-coset-wreath-from-commutant-collapse
kind: route
title: Relative-commutant collapse directly makes the coset Bernoulli wreath group nonhyperlinear
target: non-hyperlinear-group
requires:
  - relative-commutant-collapse-for-sl2-pair
  - coset-bernoulli-ce-refutes-relative-commutant-collapse
---

Take

```text
C=SL_2(Z),
A=SL_2(Z[1/2]),
W=(direct_sum_(A/C) C_2) rtimes A.                     (CW1)
```

Its group von Neumann algebra is the generalized Bernoulli crossed product

```text
L(W)=L^infinity({-1,1}^(A/C)) rtimes A.                (CW2)
```

If `W` were hyperlinear, `(CW2)` would be Connes embeddable.  The canonical
copy of `A` in `(CW2)` has regular trace, while the lamp at the base coset
`C` commutes with `C` and is moved by every `a notin C`.  Hence its image in
a matrix ultraproduct would satisfy

```text
pi(C)' cap M != pi(A)' cap M,
```

contradicting `relative-commutant-collapse-for-sl2-pair`.  Therefore `W` is
nonhyperlinear.

This endpoint is logically cleaner than adjoining a universal HNN stable
letter: it uses the single explicit commutant unitary already present as the
base lamp.  It does not make the missing collapse theorem easier.  Indeed,
`coset-bernoulli-ce-refutes-relative-commutant-collapse` shows that `(CW2)`
is the canonical falsification model for that theorem; its Connes
embeddability is exactly the unresolved matrix-coordinate alternative.
