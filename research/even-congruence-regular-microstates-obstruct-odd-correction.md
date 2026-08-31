---
rg: 2
id: even-congruence-regular-microstates-obstruct-odd-correction
kind: claim
title: Even-level regular representations stay far from every odd-congruence projective correction
distinct_from:
  sl3z-regular-microstates-are-congruence-correctable: that asserted universal odd-level correction; this gives an explicit exact regular-trace countersequence.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that concerns strict correction to arbitrary exact representations; the present obstruction survives flexible padding but uses the artificial coprime-level target restriction.
---

Let `Gamma=SL_3(Z)`,
`Gamma(N)=ker(Gamma -> SL_3(Z/N Z))`, and

```text
Q_m=Gamma/Gamma(2^m),   d_m=|Q_m|,
sigma_m=lambda_(Q_m) o q_m.
```

Then `sigma_m` is an exact representation and, for every fixed
`g != e`, `tr_(d_m)(sigma_m(g))=0` for all sufficiently large `m`.
Thus `(sigma_m)` is a regular-trace microstate sequence.

We prove that it has no flexible projective correction through odd levels.
Suppose otherwise. After padding by `k_m=o(d_m)` trivial dimensions, put

```text
D_m=d_m+k_m,
U_m=sigma_m direct_sum 1_(k_m).
```

There are projective representations `rho_m` factoring through
`SL_3(Z/n_m Z)`, with `n_m` odd, which are generatorwise close to
`U_m` modulo scalar phases. Adjointing kills those phases. Hence the two
honest unitary representations on `H_m=M_(D_m)`,

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

```text
||T_m-I||_(2,normalized) -> 0.
```

Since every vector in `ker(T_m)` contributes one to the unnormalized
squared Hilbert--Schmidt distance from `I`,

```text
rank(T_m) = (1-o(1)) dim(H_m) = (1-o(1))D_m^2.
```

The polar part of `T_m` therefore identifies common subrepresentations of
`alpha_m` and `beta_m` of dimension `(1-o(1))D_m^2`.

Every such common subrepresentation is trivial. Indeed, its kernel contains
both `Gamma(2^m)` and `Gamma(n_m)`. Reduction modulo `2^m n_m` is
onto and, by the Chinese remainder theorem,

```text
SL_3(Z/2^m n_m Z)
  = SL_3(Z/2^m Z) x SL_3(Z/n_m Z).
```

Therefore `<Gamma(2^m),Gamma(n_m)>=Gamma`.

On the other hand the multiplicity of the trivial representation in
`alpha_m` is the dimension of the commutant of
`lambda_(Q_m) direct_sum 1_(k_m)`:

```text
dim(H_m^Gamma)
 = dim End_Gamma(lambda_(Q_m) direct_sum 1_(k_m))
 = d_m + 2k_m + k_m^2
 = o(D_m^2).
```

This contradicts the common subrepresentation of dimension
`(1-o(1))D_m^2`. Hence no odd-congruence correction exists. Direct rather
than projective correction is a fortiori impossible.

**ESTABLISHED 2026-08-31.** The obstruction is elementary: coprime
congruence kernels plus property `(T)`. It does not assert any failure of
unrestricted flexible HS correction.
