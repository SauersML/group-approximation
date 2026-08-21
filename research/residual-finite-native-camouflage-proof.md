---
rg: 2
id: residual-finite-native-camouflage-proof
kind: route
title: Tensor the native lamp packet with a separating finite quotient
target: residual-finite-camouflage-removes-native-trace-window
requires:
  - native-transfer-has-finite-trace-certificate
---

The implication `(RFC3) =>` regular qualitative transfer is immediate.
For the converse, apply `native-transfer-has-finite-trace-certificate` to
obtain a finite set `F subset A-{1}` and `L<infinity` such that

```text
e_h(rho,c) <= L(d_cc(rho,c)+sep_F(rho)).                 (RFP1)
```

Residual finiteness supplies one finite quotient `q:A->K` for which
`q(g)!=1` for every `g in F`: take the product of finitely many quotients
separating the individual elements.  Let `lambda` be the left regular
representation of `K`.  Given an arbitrary `(rho,c)`, define

```text
rho_tilde(x)=rho(x) tensor lambda(q(x)),
c_tilde=c tensor I.                                     (RFP2)
```

Every defining relator has the old matrix evaluation tensored with the
identity.  Since the second tensor factor of `c_tilde` is the identity,

```text
d_cc(rho_tilde,c_tilde)=d_cc(rho,c).                    (RFP3)
```

The native target product also loses the quotient factor by literal
cancellation:

```text
c_tilde rho_tilde(h)c_tilde rho_tilde(h)^*
 =(c rho(h)c rho(h)^*) tensor I,
```

and hence

```text
e_h(rho_tilde,c_tilde)=e_h(rho,c).                      (RFP4)
```

The involution, self-adjointness, and balance conditions are preserved.
For every `g in F`, however, the regular character of `K` gives

```text
tr(rho_tilde(g))
 =tr(rho(g)) tr(lambda(q(g)))=0,                        (RFP5)
```

so `sep_F(rho_tilde)=0`.  Apply `(RFP1)` to the amplified tuple and use
`(RFP3)--(RFP5)` to obtain `(RFC3)` for the original arbitrary tuple.

For `SL_3(Z[1/2])`, write each nonidentity element of a finite set as a
matrix over `Z[1/2]`.  Choose an odd prime avoiding one nonzero numerator
from each difference `g-I`; reduction modulo that prime is defined and
keeps all those elements nonidentity.  Thus the separating quotient used
above is available directly, with no appeal to an ineffective residual-
finiteness theorem.
