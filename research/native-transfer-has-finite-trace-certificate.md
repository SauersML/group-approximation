---
rg: 2
id: native-transfer-has-finite-trace-certificate
kind: claim
title: Native regular transfer is equivalent to one finite trace-window inequality
distinct_from:
  projective-transfer-linear-bound-equals-no-ultraproduct-leak: that treats arbitrary unitaries and arbitrary trace profiles; this preserves the balanced commuting-conjugate lamp packet and obtains a certificate only on the regular-trace class actually consumed downstream.
  commuting-conjugate-involution-transfer-for-sl3-pair: that is the qualitative arithmetic assertion; this proves an exact quantitative and finite-window equivalence without deciding whether the assertion holds.
---

ESTABLISHED.  Fix a finite presentation `A=<X|R>`, words for
`C=<S_C>` and `h`, and normalized Hilbert--Schmidt norm.  For an assignment
`rho:X->U(d)` and an exact trace-zero self-adjoint involution `c`, put

```text
d_cc(rho,c)
 = max_(r in R)||rho(r)-I||_2
   + sum_(s in S_C)||[c,rho(s)]-I||_2
   + ||[c,rho(h)c rho(h)^*]-I||_2,                       (NTC1)

e_h(rho,c)=1-|tr(c rho(h)c rho(h)^*)|^2,                 (NTC2)

sep_F(rho)=max_(1!=g in F)|tr(rho(g))|                   (NTC3)
```

for a finite set of nontrivial words `F` in `A`.  The following are
equivalent.

1. Every regular-trace matrix-microstate sequence with `d_cc->0` has
   `e_h->0`; this is the qualitative native transfer in
   `commuting-conjugate-involution-transfer-for-sl3-pair`.
2. There are one finite trace window `F subset A-{1}` and one
   `L<infinity` such that, in every matrix dimension,

   ```text
   e_h(rho,c) <= L(d_cc(rho,c)+sep_F(rho)).               (NTC4)
   ```

The same equivalence holds after allowing the approximate involution and
balance defects in `(CCI1)`: Hilbert--Schmidt spectral rounding makes `c` an
involution, and tensoring once with `diag(1,-1)` makes it exactly trace zero
without changing any commutator or target energy.

In the exact jointness case, with

```text
P=(I-c)/2,       Q=rho(h)P rho(h)^*,       a=tr(PQ),
```

the certificate is the explicit four-atom inequality

```text
8a(1-2a) <= L(d_cc+sep_F).                               (NTC5)
```

Thus the native route has neither a separate quantitative-modulus problem
nor an intrinsically infinite character-test problem.  A proof may target
one finite list of actor/root trace separations and one linear matrix
inequality.  This is strictly weaker in scope than
`projective-trace-square-transfer-for-sl3-pair`, which quantifies over every
unitary and every trace profile.

The certificate is necessarily matrix-only.  In the exact coset Bernoulli
crossed product the actor trace is regular, `d_cc=sep_F=0` for every finite
`F`, and `a=1/4`, so `(NTC5)` fails maximally.  Consequently a proof of
`(NTC4)` would simultaneously give a finite trace-window obstruction to
Connes embedding for that particular commuting-conjugate lamp model.
