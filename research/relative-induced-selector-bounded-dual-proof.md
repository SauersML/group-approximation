---
rg: 2
id: relative-induced-selector-bounded-dual-proof
kind: route
title: Separate the relative induced matrix range with a bounded matrix
target: relative-induced-selector-gap-has-bounded-dual-witness
requires:
  - every-relative-ucp-window-lives-in-one-induced-representation
---

Let `U` be the set of ucp maps

```text
Theta:C*(G) -> M_d
```

whose restriction to `C*(B)` is the representation `beta`. This set is
nonempty: compression of `Ind_B^G(beta)` to the canonical identity-coset
copy gives one member. Since both algebras are finite-dimensional, the set
of ucp maps is compact, and the core constraints are closed affine
constraints. Hence `U` is compact and convex.

Evaluation at `u_x` is linear. Therefore

```text
K={Theta(u_x):Theta in U}
```

is compact and convex. The universal induced-representation theorem gives
the second description in (BDW1); in particular, it explains why the
apparently nonconvex Stiefel compression formula nevertheless has convex
image.

Equip `M_d` with the real Hilbert inner product

```text
<Y,A> = Re tr_d(Y* A)
```

and its normalized Hilbert--Schmidt norm. For any `Y` of norm at most
one and any `A in K`,

```text
<Y,X>-h(Y) <= <Y,X-A> <= ||X-A||_(2,d).
```

Taking the infimum over `A` proves that the right side of (BDW2) is at
most `Delta(X)`.

Let `A_0` be the metric projection of `X` onto the closed convex set
`K`, and suppose

```text
delta=||X-A_0||_(2,d)>0.
```

The projection characterization gives

```text
Re tr_d((X-A_0)*(A-A_0)) <= 0             for every A in K.  (BDP1)
```

Set

```text
Y=(X-A_0)/delta.
```

Then `||Y||_(2,d)=1`, (BDP1) says that `A_0` maximizes the support
functional in direction `Y`, and consequently

```text
h(Y)=Re tr_d(Y*A_0),
Re tr_d(Y*X)-h(Y)=delta.                               (BDP2)
```

This proves (BDW2). Every value of a ucp map at a unitary is a contraction,
so `||A_0||_op<=1`. If `X` is unitary, then

```text
||Y||_op
 <= (||X||_op+||A_0||_op)/delta
 <= 2/delta,                                           (BDP3)
```

which proves (BDW3).

For completeness, the support function is an explicit finite SDP. Decompose

```text
C*(G) = direct_sum_(pi in Irr(G)) M_(n_pi)
```

and choose matrix units `e_(ij)^pi`. A cp map is represented by the
positive Choi blocks

```text
C_pi=[Theta(e_(ij)^pi)]_(i,j) >= 0.
```

Unitality and exactness on the core are the linear equations

```text
sum_(pi,i) Theta(e_(ii)^pi)=I,

sum_(pi,i,j) pi(b)_(ij) Theta(e_(ij)^pi)=beta(b)
                                                   for every b in B. (BDP4)
```

The objective

```text
Re tr_d(Y* sum_(pi,i,j) pi(x)_(ij) Theta(e_(ij)^pi))
```

is linear in the Choi blocks. Its maximum is `h(Y)`. This verifies the
complete-order and finite-semidefinite assertions without choosing a
Stiefel coordinate chart.

A relative Pauli square checks the formula sharply. Take

```text
G=C2 x C2=<a,b | a^2=b^2=1, ab=ba>,
B=<a>,       beta(a)=X=[[0,1],[1,0]],
target X_b=Z=[[1,0],[0,-1]].
```

For every feasible `Theta`, the unitary `Theta(u_a)=X` puts `u_a`
in the multiplicative domain. Hence

```text
X Theta(u_b)=Theta(u_b) X.
```

Every feasible coefficient therefore commutes with `X` and is
Hilbert--Schmidt orthogonal to `Z`. The canonical induced coefficient at
`b` is zero, so

```text
Delta_(G,B,beta)(Z)=1.                                 (BDP5)
```

The dual witness is exactly `Y=Z`: it has normalized HS norm and operator
norm one, `h(Z)=0`, and `tr_2(Z*Z)=1`. Thus the abstract separator is a
literal missing cross-difference relation in the smallest example.

Finally, apply the argument coordinatewise. If `Delta_n` does not tend
to zero, pass to a subsequence on which `Delta_n>=epsilon`. Equations
(BDP2)--(BDP3) produce `Y_n` with normalized HS norm one, operator norm
at most `2/epsilon`, and dual gap at least `epsilon`. Conversely any
such dual gap is bounded above by `Delta_n` by the first inequality in
the proof. This is precisely the equivalence (BDW4).
