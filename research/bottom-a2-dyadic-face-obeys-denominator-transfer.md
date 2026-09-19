---
rg: 2
id: bottom-a2-dyadic-face-obeys-denominator-transfer
kind: claim
title: The bottom A2 dyadic face obeys an explicit denominator transfer inequality
distinct_from:
  involutory-opposite-root-face-obeys-projective-transfer: that assumes direct control of the two opposite long-root squares and their U-centralities; this derives those inputs from simple-root Steinberg packets in two opposite A2 chambers.
  involutory-steinberg-simple-root-forces-long-root-involution: that treats one chamber and concludes only long-root involutivity; this combines two opposite chambers with the rank-one denominator word and reaches the target commutator.
  projective-trace-square-transfer-for-sl3-pair: that must handle arbitrary conductor and the whole presentation; this closes only the bottom exponent-two A2 stratum and explicitly identifies every defect through which a deeper-conductor enemy must escape.
---

Let `U,H,p,q,a,r,s,b` be matrix unitaries. Put

```text
c_a=[p,q],       c_b=[r,s],
gamma_a=||a-c_a||_2,       gamma_b=||b-c_b||_2,
kappa_a=||p a p^*-a||_2,   kappa_b=||r b r^*-b||_2,
sigma_a=||p^2-I||_2,       sigma_b=||r^2-I||_2,
epsilon_p=||Up-pU||_2,     epsilon_q=||Uq-qU||_2,
epsilon_r=||Ur-rU||_2,     epsilon_s=||Us-sU||_2.        (BA1)
```

Define the two chamber budgets

```text
D_a=4 gamma_a+kappa_a+2 sigma_a,
D_b=4 gamma_b+kappa_b+2 sigma_b,
E_a=2 gamma_a+2 epsilon_p+2 epsilon_q,
E_b=2 gamma_b+2 epsilon_r+2 epsilon_s.                   (BA2)
```

For the rank-one denominator residual put

```text
eta=||H-a^2(H b^(-2)H^*)a b a^*||_2.                    (BA3)
```

Then

```text
||UHU^*H^*-I||_2
 <=2 eta+2D_a+2D_b+2E_a+E_b.                            (BA4)
```

All constants are independent of matrix dimension. In particular, exact
Steinberg relations in the two opposite chambers, exact centrality of their
shared long roots, involutivity of the selected simple roots, exact
`U`-centrality of the four simple roots, and the exact denominator identity
force `[U,H]=1`.

This is the smallest currently proved arithmetic-specific transfer layer.
It depends only on two opposite A2 commutator cells and the rank-one Weyl
decomposition. It does not handle a deep dyadic sector because `sigma_a` or
`sigma_b` may then be macroscopic. Consequently the open hexagon decoder
can be narrowed to proving that any projective leak either has negligible
deep-root square defect after conductor localization or pays a shared-root
leakage term; the bottom face itself is now closed by `(BA4)`.

