---
rg: 2
id: finite-window-presentation-witness-proof
kind: route
title: Present the universal group of a forbidden finite multiplication window
target: nonhyperlinearity-has-a-finite-presentation-witness
requires: []
---

Use the finite-window formulation of hyperlinearity.  Since `G` is not
hyperlinear, there are a finite set `F subset G`, containing `1`, and
`epsilon_0>0` such that no finite-dimensional unitary family indexed by
`F` is simultaneously `epsilon_0`-multiplicative on every product visible
inside `F` and `epsilon_0`-separating on the distinct elements of `F`.

Introduce one generator `x_g` for every `g in F` and impose the finite
partial multiplication table

```text
x_1=1,
x_g x_h=x_k       whenever g,h,k in F and gh=k in G.          (FPW2)
```

Let `K` be the resulting finitely presented group.  Evaluation
`x_g |-> g` defines a homomorphism

```text
pi:K -> <F> <= G.                                             (FPW3)
```

In particular, if `g!=h` in `F`, then `x_g!=x_h` in `K`, since an equality
would remain an equality after applying `pi`.

Suppose `K` were hyperlinear.  Apply its microstate property to the finite
set `{x_g:g in F}` with accuracy smaller than `epsilon_0`.  Relabel the
resulting matrices by `g`.  Relations `(FPW2)` give precisely the required
multiplicativity conditions on every product visible in `F`, while the
distinctness just proved gives the required normalized-HS separation after
taking the microstate accuracy sufficiently small.  This is a forbidden
microstate for the chosen window of `G`, a contradiction.  Hence `K` is
nonhyperlinear.

The reverse implication in `(FPW1)` is immediate.
