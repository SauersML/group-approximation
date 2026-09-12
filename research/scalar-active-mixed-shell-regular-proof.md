---
rg: 2
id: scalar-active-mixed-shell-regular-proof
kind: route
title: Embed the scalar active shell in a finite elementary group and take its regular representation
target: scalar-active-mixed-shell-has-marked-regular-model
requires: []
---

For `M,N in M_n(k)`, idempotence of `A` gives

```text
[I+(M-I)A][I+(N-I)A]
 =I+[(M-I)+(N-I)+(M-I)(N-I)]A
 =I+(MN-I)A.                                           (SMP1)
```

Thus `Phi_A(M)Phi_A(N)=Phi_A(MN)`, and
`Phi_A(M)^(-1)=Phi_A(M^(-1))`.  If `Phi_A(M)=I`, every coefficient
`(M_ij-delta_ij)A` is zero.  Since `A!=0` and `k` is a field, the scalar map
`k -> R`, `c |-> cA`, is injective.  Hence `M=I`, proving injectivity.

For an elementary transvection,

```text
Phi_A(I+cE_ij)=I+cAE_ij=x_ij(cA).                      (SMP2)
```

Therefore `(SAM2)` is the image of `E_n(k)` and is finite.  Every stipulated
mixed-root, Weyl, Whitehead, or return relator in the claim is an equality
inside this literal finite matrix group, so its left regular representation
satisfies the relator exactly.

Finally

```text
x_ij(cA)^m=x_ij(mcA).                                  (SMP3)
```

For `c!=0`, injectivity of `kA` shows that the least positive `m` for which
this is the identity is `p=char(k)`.  A nonidentity regular translation has
trace zero, which gives the first two formulas in `(SAM4)`.  Its action on
the finite group partitions the regular basis into `p`-cycles.  Each
`p`-th root of unity consequently occurs with the same multiplicity, so the
nontrivial spectral carrier has trace `(p-1)/p`.
