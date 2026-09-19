---
rg: 2
id: native-transfer-has-defect-only-certificate
kind: claim
title: Native regular transfer is equivalent to one universal defect-only inequality
distinct_from:
  projective-transfer-linear-bound-equals-no-ultraproduct-leak: that treats arbitrary unitaries and arbitrary trace profiles; this preserves the balanced commuting-conjugate lamp packet and uses residual-finite camouflage to remove the regular-trace restriction.
  commuting-conjugate-involution-transfer-for-sl3-pair: that is the qualitative arithmetic assertion; this proves an exact quantitative equivalence without deciding whether the assertion holds.
  canonical-trace-does-not-weaken-thin-commutant-transfer: that treats an arbitrary auxiliary unitary and ordinary subgroup commutators; this verifies the tensor camouflage for the native trace-zero involution, its commuting-conjugate relation, and the balanced four-atom target.
---

ESTABLISHED.  Fix a finite presentation `A=<X|R>` of a residually finite
group, words for `C=<S_C>` and `h`, and normalized Hilbert--Schmidt norm.
For an assignment `rho:X->U(d)` and an exact trace-zero self-adjoint
involution `c`, put

```text
d_cc(rho,c)
 = max_(r in R)||rho(r)-I||_2
   + sum_(s in S_C)||[c,rho(s)]-I||_2
   + ||[c,rho(h)c rho(h)^*]-I||_2,                       (NDC1)

e_h(rho,c)=1-|tr(c rho(h)c rho(h)^*)|^2.                 (NDC2)
```

The following are equivalent.

1. Every regular-trace matrix-microstate sequence with `d_cc->0` has
   `e_h->0`.
2. There is `L<infinity` such that, in every matrix dimension and for every
   assignment and balanced involution as above,

   ```text
   e_h(rho,c) <= L d_cc(rho,c).                          (NDC3)
   ```

The same equivalence holds after adding the approximate involution,
self-adjointness, and balance defects: spectral rounding and one external
balanced bit reduce to the displayed exact format.

In the exact jointness case, with

```text
P=(I-c)/2,       Q=rho(h)P rho(h)^*,       a=tr(PQ),
```

the certificate is the explicit four-atom inequality

```text
8a(1-2a) <= L d_cc(rho,c).                              (NDC4)
```

For `A=SL_3(Z[1/2])`, residual finiteness is explicit by reduction modulo
odd primes.  Thus the native route has no separate quantitative-modulus
problem, no infinite character-test problem, and not even a finite actor
trace window.  Canonical actor trace supplies no extra rigidity: every
noncanonical finite-matrix failure of `(NDC3)` can be camouflaged, without
changing its defect or four-atom overlap, into a regular-trace failure.

The inequality remains matrix-only.  In the exact coset Bernoulli crossed
product the actor trace is regular, `d_cc=0`, and `a=1/4`, so `(NDC4)` fails
maximally.  A proof must use finite-matrix arithmetic on the common four
atoms, not a tracial identity or character-selection argument.
