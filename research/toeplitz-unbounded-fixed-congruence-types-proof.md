---
rg: 2
id: toeplitz-unbounded-fixed-congruence-types-proof
kind: route
title: Collapse the Toeplitz defect over finite fields and use projective augmentation representations
target: toeplitz-self-embedding-fixes-unbounded-congruence-types
requires:
  - toeplitz-head-tail-unital-self-embedding
  - kazhdan-bounded-types-form-central-summand
---

For `q=2^n`, choose a multiplicative generator `zeta_q` of `F_q^x` and
define

```text
theta_q:T->F_q,       x |-> zeta_q,       y |-> zeta_q^-1.  (1)
```

This map is onto because `F_2[zeta_q]=F_q`.  Since the target is
commutative,

```text
theta_q(1+xy)=0,
theta_q(sigma(a))=zeta_q theta_q(a) zeta_q^-1
                  +epsilon(a) theta_q(1+xy)
                =theta_q(a).                              (2)
```

Hence the quotient

```text
bar_theta_q:Gamma->EL_r(F_q)=SL_r(F_q)                    (3)
```

satisfies `bar_theta_q o alpha=bar_theta_q`.

The action of `SL_r(F_q)` on the projective points of `F_q^r` is
2-transitive for `r>=3`.  Indeed a linear map can send any ordered pair of
distinct lines to any other, and its determinant can be corrected on a
third basis direction without changing those two target lines.  Therefore
the complex permutation representation is

```text
1 direct_sum eta_q,       dim(eta_q)=N_q-1,
N_q=(q^r-1)/(q-1),                                         (4)
```

with `eta_q` irreducible: 2-transitivity says that the permutation
character has squared norm two, so its augmentation character has squared
norm one.

Inflate `eta_q` through `(3)` and call the result `rho_q`.  Equations
`(2)`--`(3)` give `rho_q o alpha=rho_q`, while `(4)` makes its dimension
tend to infinity.  Taking `q` large enough gives `(TUC2)` and permits the
stable letter to act as the identity.  Irreducibility gives
`End_Gamma(rho_q)=C`, hence the adjoint commutant density is
`1/dim(rho_q)^2`.  Since its sole irreducible constituent has degree above
`K`, the defining property of `p_<=K` gives `rho_q(p_<=K)=0`.
