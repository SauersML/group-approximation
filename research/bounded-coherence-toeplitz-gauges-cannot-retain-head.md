---
rg: 2
id: bounded-coherence-toeplitz-gauges-cannot-retain-head
kind: claim
title: Bounded noncommutative coherence cannot repair the Toeplitz Jacobson head
distinct_from:
  scalar-rephased-toeplitz-sections-still-collapse-head: that treats scalar one-cochains; this allows mutually noncommuting matrix gauges in every finite-group isotypic multiplicity space
  bounded-block-jacobson-microstates-also-collapse: that assumes the entire approximate tuple has bounded irreducible degree; here the finite-group carrier may have arbitrarily large irreducible blocks and only its commutant multiplicities are bounded
  toeplitz-folner-compressions-cannot-retain-jacobson-head: that treats an ungauged finite-section representation; this permits generator-dependent nonscalar perturbations
---

Fix the standard Tietze-expanded finite presentation
`P=<Sigma | R>` of `EL_28(J)`, where

```text
J=F_2<S,T | TS=1>,
```

and fix the marked Jacobson head word `w`. Let

```text
theta_N: Sigma -> F_N=GL_(28N)(F_2)
```

be the literal truncated-Toeplitz section. For an arbitrary
finite-dimensional unitary representation `rho:F_N->U(H)`, write its
isotypic decomposition as

```text
H = directSum_lambda V_lambda tensor C^(m_lambda),
rho = directSum_lambda pi_lambda tensor I_(m_lambda).
```

Choose arbitrary unitaries

```text
Z_s in rho(F_N)'                    (s in Sigma)
```

and put `U_s=rho(theta_N(s))Z_s`. The gauges `Z_s` need not commute
with one another.

For every fixed `K` there is a modulus `Omega_K(epsilon)->0`, independent
of `N`, `rho), `dim(H)), and the number and dimensions of the
`pi_lambda), such that

```text
max_lambda m_lambda <= K
and
delta(U)=max_(r in R) ||r(U)-I||_2 <= epsilon
imply
||w(U)-I||_2 <= Omega_K(epsilon).                       (BCT1)
```

Thus the smallest Pauli repair, `m_lambda=2`, and every other bounded
off-diagonal bundle fail even when their generator gauges are fully
noncommutative.

The point is not a scalar or projective reduction. A character gap for
transvections first forces the large finite-group carrier to pay for its
Toeplitz endpoint. What remains is an approximate Jacobson tuple entirely
inside the multiplicity algebra; bounded multiplicity then collapses its
head.

This result does not cover `m_lambda->infinity`, nor perturbations that do
not lie in `rho(F_N)'` and hence mix inequivalent finite-group isotypes.
Those are the two surviving coherence mechanisms.

DERIVATION
commutator-character-gap-and-endpoint-filling-proof
