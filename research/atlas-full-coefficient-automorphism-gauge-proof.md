---
rg: 2
id: atlas-full-coefficient-automorphism-gauge-proof
kind: route
title: Classify full matrix star automorphisms and absorb their implementers into chart gauge
target: atlas-full-coefficient-automorphism-twists-are-gauge
requires:
  - atlas-full-relator-data-factor-through-double-commutant-gauge
---

Let `alpha` be as in `(FCA2)`.  Since `alpha` preserves the center and is
real-linear and multiplicative,

```text
alpha(i I)=i I       or       alpha(i I)=-i I.        (FCAP1)
```

In the first case `alpha` is complex-linear.  Skolem--Noether gives an
invertible `S` with `alpha(X)=SXS^(-1)`.  Star preservation implies

```text
S^* S X = X S^* S       for every X in M_r(C),        (FCAP2)
```

so `S^*S` is scalar.  Rescaling `S` gives a unitary `V`, and
`alpha=Ad(V)`.

In the second case compose `alpha` with entrywise complex conjugation
`kappa`.  The map `kappa alpha` is a complex-linear star automorphism, hence
is `Ad(V)` for a unitary `V`.  Replacing `V` by its conjugate if necessary
gives

```text
alpha(X)=V conjugate(X) V^*.                          (FCAP3)
```

Applying `(FCAP2)` or `(FCAP3)` to every block proves `(FCA3)` or `(FCA4)`.
The unitary `I tensor V` commutes with `lambda(A) tensor I`; therefore the
first case is exactly the double-commutant gauge from
`atlas-full-relator-data-factor-through-double-commutant-gauge`, and all word
values are unitarily conjugate.

In the second case, every `lambda(a)` is a real permutation matrix.  Hence,
before the harmless `I tensor V` conjugacy,

```text
pi_(conjugate U)(w)=conjugate(pi_U(w))                (FCAP4)
```

for every literal word `w`.  Entrywise conjugation preserves singular
values and normalized Hilbert--Schmidt norm, proving `(FCA5)`.

The use of automorphisms is essential to the scope.  A complex-linear
anti-automorphism such as transpose reverses products and therefore is not a
blockwise multiplicative transport of the Atlas word evaluation.  Applying
different maps at different block positions is likewise not an
automorphism of the coefficient algebra and receives no unitarity or
relator preservation from this argument.
