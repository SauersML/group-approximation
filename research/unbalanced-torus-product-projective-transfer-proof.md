---
rg: 2
id: unbalanced-torus-product-projective-transfer-proof
kind: route
title: Compare with the untwisted exact actor and charge the multiplicity factor by the torus word
target: unbalanced-torus-relator-closes-product-projective-sector
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
  - two-torus-closures-detect-denominator-multiplicity
---

Put

```text
H_0=I_M tensor sigma(h).
```

The assignment `g mapsto I_M tensor sigma(g)` is an exact representation
of `A`.  The proof of
`exact-projective-codensity-has-a-uniform-trace-square-gap` gives a constant
`K_0`, independent of all matrix dimensions and multiplicities, for which

```text
||[U,H_0]-I||_2^2 <= K_0 q_C(U).                        (UPP1)
```

This is the ordinary-commutator estimate obtained there after the fixed
perfectness words remove the source phases and the Kazhdan projection lands
in the common commutant of `C` and `A`.

The explicit evaluation in
`two-torus-closures-detect-denominator-multiplicity` is

```text
ev_(X,H)(R_tor)=V^(-1) tensor I_K.
```

Consequently

```text
eta=||V-I||_2=||H-H_0||_2.                              (UPP2)
```

For arbitrary unitaries `U,H,H_0`, a two-term telescope gives

```text
||[U,H]-[U,H_0]||_2 <= 2||H-H_0||_2.                   (UPP3)
```

Therefore

```text
||[U,H]-I||_2
 <= sqrt(K_0 q_C(U))+2 eta,

||[U,H]-I||_2^2
 <= 2K_0 q_C(U)+8 eta^2.                               (UPP4)
```

Finally every unitary `W` satisfies

```text
1-|tr(W)|^2 <= ||W-I||_2^2.                            (UPP5)
```

Taking `W=[U,H]` in `(UPP5)` and using `(UPP4)` proves `(UTP4)` with
`K=2K_0`.
