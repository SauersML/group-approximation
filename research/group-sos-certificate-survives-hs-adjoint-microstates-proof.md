---
rg: 2
id: group-sos-certificate-survives-hs-adjoint-microstates-proof
kind: route
title: Evaluate the SOS identity through the adjoint defect map
target: group-sos-certificate-survives-hs-adjoint-microstates
requires: []
---

First compare adjoint actions.  For unitaries `U,V in U(d)`, put
`a=tau_d(U*V)`.  The normalized trace of `Ad_(U*V)` on the `d^2`-dimensional
Hilbert space `M_d` is `|a|^2`, so

```text
||Ad_U-Ad_V||_(2,H)^2 = 2-2|a|^2.
```

Since `|a|^2 >= (Re a)^2`,

```text
2-2|a|^2
 <= 2-2(Re a)^2
 <= 2(2-2 Re a)
 = 2 d_2(U,V)^2.
```

Hence every tested multiplicative defect of `phi` gives

```text
||T_g T_h-T_(gh)||_(2,H) <= sqrt(2) delta.             (1)
```

For finitely supported group-algebra elements
`u=sum_g u_g g`, `v=sum_h v_h h` whose products lie in the tested window,
expand and use the triangle inequality:

```text
||L_phi(u)L_phi(v)-L_phi(uv)||_(2,H)
 <= sum_(g,h) |u_g| |v_h| ||T_gT_h-T_(gh)||_(2,H)
 <= sqrt(2) delta ||u||_1 ||v||_1.                     (2)
```

Inverse normalization gives `T_(g^(-1))=T_g*`, hence

```text
L_phi(u*)=L_phi(u)*.                                    (3)
```

Now apply `(2)` to `(Delta,Delta)` and to every `(xi_j*,xi_j)`.  Because
`L_phi` is linear, the exact coefficient identity `(SOS)` gives

```text
L_phi(Delta^2-kappa Delta-sum_j xi_j*xi_j)=0.
```

Using `(3)` and adding/subtracting those linear evaluations,

```text
A^2-kappa A-sum_j X_j*X_j
 = [A^2-L_phi(Delta^2)]
   -sum_j [X_j*X_j-L_phi(xi_j*xi_j)].
```

Therefore `(2)` yields

```text
||A^2-kappa A-sum_j X_j*X_j||_(2,H)
 <= sqrt(2) delta
      (||Delta||_1^2 + sum_j ||xi_j||_1^2),
```

which is `(ASOS)`.

Finally suppose `Delta=sum_(s in S)(1-s)` for an inverse-closed finite set
`S`.  Then `sum_s T_s` is self-adjoint, and for every `z in H`,

```text
<Az,z>
 = (1/2) sum_(s in S) ||T_s z-z||_2^2 >= 0.
```

Thus `A>=0`, as claimed.
