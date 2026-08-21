---
rg: 2
id: residual-finite-camouflage-removes-native-trace-window
kind: claim
title: Residual-finite camouflage removes the actor trace window from native commuting-involution transfer
distinct_from:
  native-transfer-has-finite-trace-certificate: that reduces regular native transfer to a linear inequality with one finite actor trace window; this tensors by a separating finite quotient and proves that the window can be deleted altogether.
  canonical-trace-does-not-weaken-thin-commutant-transfer: that treats an arbitrary auxiliary unitary and ordinary subgroup commutators; this verifies that the camouflage preserves the native trace-zero involution, its commuting-conjugate relation, and the balanced four-atom target exactly.
  projective-transfer-linear-bound-equals-no-ultraproduct-leak: that gives a defect-only inequality for universal projective commutant transfer; this gives the analogous conclusion only for the strictly narrower native commuting-conjugate involution packet.
---

ESTABLISHED.  Let `A=<X|R>` be residually finite, let
`C=<S_C><=A`, and fix `h in A`.  For an assignment
`rho:X->U(d)` and an exact trace-zero self-adjoint involution `c`, put

```text
d_cc(rho,c)
 = max_(r in R)||rho(r)-I||_2
   + sum_(s in S_C)||[c,rho(s)]-I||_2
   + ||[c,rho(h)c rho(h)^*]-I||_2,                       (RFC1)

e_h(rho,c)=1-|tr(c rho(h)c rho(h)^*)|^2.                 (RFC2)
```

Then the following are equivalent.

1. Every regular-trace matrix-microstate sequence with `d_cc->0` has
   `e_h->0`.
2. There is `L<infinity` such that, in every matrix dimension and for
   every assignment and balanced involution as above,

   ```text
   e_h(rho,c) <= L d_cc(rho,c).                          (RFC3)
   ```

For `A=SL_3(Z[1/2])`, residual finiteness is explicit by reduction modulo
odd primes.  Consequently the OPEN native transfer
`commuting-conjugate-involution-transfer-for-sl3-pair` has no residual
trace-profile qualification and no actor trace window.  In the exact
commuting case, with

```text
P=(I-c)/2,       Q=rho(h)P rho(h)^*,       a=tr(PQ),
```

its complete finite-dimensional endpoint is the dimension-free inequality

```text
8a(1-2a) <= L d_cc(rho,c).                              (RFC4)
```

This does not prove `(RFC3)`.  It shows that canonical actor traces cannot
be used as extra leverage: any noncanonical finite-matrix failure can be
camouflaged, without changing either side of `(RFC3)`, into a regular-trace
failure.  The remaining input must therefore be a genuinely matrix-coordinate
arithmetic estimate on the common four atoms, not a character-selection or
finite-window argument.
