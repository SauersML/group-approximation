---
rg: 2
id: boolean-predicate-central-phase-word-proof
kind: route
title: Evaluate algebraic-normal-form monomials by unitriangular commutators
target: boolean-predicate-central-phase-word
requires:
  - gowers-hatami-finite-group-hs-stability
---

For a degree-`d` monomial use the standard chain of elementary transvections
in `UT_(d+1)(F_2)`. For every assignment `a`, place one copy of this finite
group in the `a`-coordinate of a finite direct product, and let each input
generator be the tuple whose `a`-coordinate is its elementary transvection
exactly when the corresponding bit of `a` is one. Repeatedly applying

```text
[I+a E_(i,i+1), I+b E_(i+1,i+2)]
  = I+ab E_(i,i+2)
```

shows that evaluation at coordinate `a` sends the left-normed commutator to
the central top transvection exactly when every input bit is one. Take one
unitriangular block for every monomial and let `H_f` be the subgroup generated
by these input tuples inside the finite assignment-by-monomial product.
Evaluation at `a`, followed by tensoring irreducible block representations in
which each top transvection acts as `-I`, is the model `pi_a`. Central factors
commute, so `W_f` acts by the parity of active monomials, namely
`(-1)^(f(a))`.

A subgroup of a finite direct product of finite `2`-groups is a finite
`2`-group. The construction is fixed once `f` is fixed, giving uniform size.
The constant monomial, when present, is one additional central `C_2` factor.
The prerequisite supplies the stated flexible normalized-HS transport for the
resulting fixed finite group.
