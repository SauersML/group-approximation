---
rg: 2
id: schur-child-toeplitz-morita-wire
kind: claim
title: The two Schur children and one Toeplitz head actuator form an exact multiplicity Morita wire
distinct_from:
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out direct unitary conjugacy of packet restrictions; this returns the doubled multiplicity through two transverse child commutants instead.
  toeplitz-tail-retains-contextual-schur-density: that asks for the quantitative normalized-HS density dichotomy; this proves the exact finite-dimensional algebra through which that dichotomy must run.
---

Let `A_f<=B_f` be a Schur packet and let

```text
B_f^P=<A_f,p_(N+1)>,       B_f^Q=<A_f,q_(N+1)>
```

be its two children. On every active selector sector, write a full packet
isotypic block as

```text
T tensor M = S tensor C^2 tensor M,                            (STM1)
```

where `A_f` acts on `S`, the relative Pauli pair acts on `C^2`, and `M` is
the external multiplicity space. Then the four commutants are

```text
Comm(A_f)   = M_2 tensor End(M),
Comm(B_f^P) = MASA_P tensor End(M),
Comm(B_f^Q) = MASA_Q tensor End(M),
Comm(B_f)   = I_2 tensor End(M),                               (STM2)
```

where `MASA_P` and `MASA_Q` are transverse Pauli MASAs. In particular,

```text
Alg(Comm(B_f^P),Comm(B_f^Q))=Comm(A_f).                        (STM3)
```

Under the explicit embedding of `schur-child-crosses-toeplitz-compressor`,
the `Q` child lies in the compressed Toeplitz tail and the missing transverse
Pauli actuator lies in the head. Since one fixed head swap together with the
tail generates the whole Toeplitz ring, the two charts in `(STM2)` give an
exact, finitely actuated Morita return of the doubled `A_f` multiplicity
space. This return is not a stable-letter conjugacy and is therefore not
blocked by `hnn-conjugacy-cannot-return-schur-morita-multiplicity`.

The theorem is algebraic. It does not say that a positive normalized-adjoint
density in one child commutant survives the residual tail action; that is the
remaining analytic content of `toeplitz-tail-retains-contextual-schur-density`.

