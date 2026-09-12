---
rg: 2
id: dense-offdiagonal-leavitt-heisenberg-proof
kind: route
title: Add the constant root path and compute the complementary prefix form
target: dense-offdiagonal-leavitt-heisenberg-packet
requires:
  - leavitt-prefixes-form-exponential-heisenberg-packet
---

Write the nilpotent coefficients in matrix notation as

```text
U_alpha=A E_12+t_alpha E_13,
V_beta =A E_24+s_beta E_34.
```

Then `U_alpha^2=V_beta^2=V_beta U_alpha=0`, while

```text
U_alpha V_beta
 =(A+t_alpha s_beta)E_14
 =(1+delta_(alpha,beta))A E_14.
```

In characteristic two, `I+U_alpha` and `I+V_beta` are involutions and their
commutator is `I+U_alpha V_beta`, proving `(DOL2)`.  Products of two `U`'s,
or two `V`'s, vanish, so the two named families commute.  The root `14`
commutes with all four roots used above.

For invertibility, if `Kx=0` then

```text
x=(sum_i x_i) 1.
```

If the scalar on the right is zero then `x=0`; if it is one then summing the
coordinates gives `1=D=0` in `F_2`, a contradiction.  Thus `K` is
nondegenerate.  Finite Stone--von Neumann theory gives the divisibility
`2^D` on the negative central sector exactly as for the identity-prefix
packet.

For the cancellation statistic, unequal prefixes reduce
`t_alpha s_beta=0` at their first mismatch.  The matching-prefix length is a
truncated geometric random variable, so its first and second moments are
bounded independently of `n`.  Equal pairs have cost `n`, contributing
`n^j 2^(-n)` to the `j`th moment for `j=1,2`; these contributions are also
uniformly bounded.

