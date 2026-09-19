---
rg: 2
id: binary-jacobson-zero-toeplitz-index-proof
kind: route
title: Take the Laurent determinant and exhibit the balanced Whitehead lift
target: binary-jacobson-elementary-symbols-have-zero-toeplitz-index
requires: []
---

The units of `A=F_2[z,z^(-1)]` are exactly the monomials `z^k`, so

```text
deg:A^x->Z,                 deg(z^k)=k                  (1)
```

is a homomorphism.  Composition with the determinant gives `(BTI1)`.  Every
elementary transvection has determinant one.  Since `EL_m(A)` is generated
by elementary transvections, `(BTI2)` follows immediately.

The cancellation of the two one-sided defects is visible before passing to
`K`-theory.  In `M_2(J)` set

```text
U = [[S,Q],[0,T]],             V = [[T,0],[Q,S]].       (2)
```

The relations

```text
TS=1,       Q^2=Q,       QS=0,       TQ=0              (3)
```

give `UV=VU=I_2`.  Its Laurent symbol is

```text
mu(U)=diag(z,z^(-1)),                                    (4)
```

whose total index is `1+(-1)=0`.  This is the balanced Whitehead lift used
by the monomial-symbol subsystem; it carries no uncancelled boundary class.

Finally `x_13(Q)` is itself an elementary matrix over the finitary ideal, so
its determinant and `K_1` class are trivial.  The only basic Laurent unit
with nonzero boundary is the unbalanced `z`, while every symbol in
`EL_5(A)` has determinant one by `(BTI2)`.  Hence the ordinary Toeplitz
boundary cannot detect `(BTI3)`, proving the claim.
