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

Suppose `K` were hyperlinear.  Apply its microstate property, with accuracy
smaller than `epsilon_0`, to a finite window containing all the `x_g`, all
differences `x_g^(-1)x_h` for `g!=h`, and the products needed to evaluate
them.  (In the pairwise-separation definition of a microstate it is enough
to use just the named elements.)  Relabel the matrices assigned to `x_g`
by `g`.  Relations `(FPW2)` give precisely the required multiplicativity
conditions on every product visible in `F`.  Since every named difference
is nontrivial by `(FPW3)`, canonical trace separation gives the required
normalized-HS separation of the relabelled matrices after taking the
microstate accuracy sufficiently small.  This is a forbidden microstate for
the chosen window of `G`, a contradiction.  Hence `K` is nonhyperlinear.

The reverse implication in `(FPW1)` is immediate.
