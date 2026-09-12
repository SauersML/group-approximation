---
rg: 2
id: even-odd-adjoint-disjointness-proof
kind: route
title: Adjoint even and odd congruence towers have only trivial common summands
target: even-congruence-regular-microstates-obstruct-odd-correction
requires: []
---

For every fixed `g != e`, residual separation by the subgroups
`Gamma(2^m)` gives

```text
tr_(d_m)(sigma_m(g))=0
```

for all sufficiently large `m`. Thus `(sigma_m)` is an exact
regular-trace microstate sequence.

First use the direct-padding convention. Suppose that, for
`k_m=o(d_m)` and `D_m=d_m+k_m`,

```text
U_m=sigma_m direct_sum 1_(k_m)
```

were generatorwise close modulo scalar phases to projective
representations `rho_m` factoring through `SL_3(Z/n_m Z)`, with
`n_m` odd. Adjointing kills the phases. Hence the two honest unitary
representations on `H_m=M_(D_m)`,

```text
alpha_m=Ad(U_m),   beta_m=Ad(rho_m),
```

are generatorwise close in normalized Hilbert--Schmidt norm.

Apply property `(T)` of `Gamma` to the representation on
`Hom(H_m,H_m)` given by

```text
g . T = beta_m(g) T alpha_m(g)^*.
```

The identity map is almost invariant, so its orthogonal projection `T_m`
to the invariant subspace satisfies
`||T_m-I||_(2,normalized)->0`. Every vector in `ker(T_m)` contributes
one to the unnormalized squared Hilbert--Schmidt distance from `I`, so

```text
rank(T_m)=(1-o(1))D_m^2.
```

The polar part of `T_m` identifies common subrepresentations of
`alpha_m` and `beta_m` of that dimension.

Every common subrepresentation is trivial. Its kernel contains both
`Gamma(2^m)` and `Gamma(n_m)`. Reduction modulo `2^m n_m` is onto
and the Chinese remainder theorem gives

```text
SL_3(Z/2^m n_m Z)
  = SL_3(Z/2^m Z) x SL_3(Z/n_m Z).
```

Consequently `<Gamma(2^m),Gamma(n_m)>=Gamma`.

But the multiplicity of the trivial representation in `alpha_m` is the
dimension of the commutant of
`lambda_(Q_m) direct_sum 1_(k_m)`:

```text
dim(H_m^Gamma)
 = d_m + 2k_m + k_m^2
 = o(D_m^2).
```

This contradicts the almost-full common subrepresentation.

The isometric-corner convention gives the same contradiction without
choosing a trivial complementary block. Let
`V_m:C^(d_m)->C^(D_m)` be the correcting isometry. Compression closeness,
together with the fact that the compressed matrices are asymptotically
unitary, makes

```text
J_m:M_(d_m)->M_(D_m),   J_m(X)=V_m X V_m^*
```

an almost intertwiner from `Ad(sigma_m)` to `Ad(rho_m)`; projective
phases again disappear. Property `(T)` projects `J_m` to an exact
intertwiner of rank `(1-o(1))d_m^2`. Its polar part gives a common
subrepresentation of that dimension. Coprime-level disjointness again says
that it must be trivial, whereas the invariant space of
`Ad(lambda_(Q_m))` has dimension exactly `d_m=o(d_m^2)`. This is the
same contradiction and also covers an almost-invariant-corner formulation.
QED
