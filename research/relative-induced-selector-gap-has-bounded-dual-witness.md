---
rg: 2
id: relative-induced-selector-gap-has-bounded-dual-witness
kind: claim
title: A persistent relative induced-selector gap has a bounded complete-order witness
distinct_from:
  every-relative-ucp-window-lives-in-one-induced-representation: that parametrizes the primal relative matrix range by core-intertwining isometries; this proves its exact Hilbert--Schmidt dual and a dimension-free operator-norm bound on every persistent separator.
  finite-nuclear-quotient-does-not-complete-partial-toeplitz-data: that gives one explicit partial-window obstruction; this gives the universal separating functional for the concrete full relative selector.
---

Let `G` be finite, `B<G`, and let `beta:B -> U(d)` be a
representation. Put

```text
rho = Ind_B^G(beta),
K_(G,B,beta)(x)
  = { Theta(u_x) :
      Theta:C*(G)->M_d is ucp and Theta(u_b)=beta(b) for b in B }.
```

Equivalently, by
`every-relative-ucp-window-lives-in-one-induced-representation`,

```text
K_(G,B,beta)(x)
  = { V* rho(x) V :
      V*V=I and rho(b)V=V beta(b) for b in B }.          (BDW1)
```

Although the Stiefel parametrization in (BDW1) is nonlinear, its image
`K_(G,B,beta)(x)` is compact and convex. For `X in M_d`, define

```text
Delta(X)=dist_(2,d)(X,K_(G,B,beta)(x)),
h(Y)=sup_(A in K_(G,B,beta)(x)) Re tr_d(Y* A).
```

Then the exact dual formula is

```text
Delta(X)
 = max_(||Y||_(2,d)<=1) { Re tr_d(Y*X)-h(Y) }.          (BDW2)
```

If `X` is unitary and `Delta(X)>0`, the maximum has a witness `Y`
satisfying

```text
||Y||_(2,d)=1,
||Y||_op <= 2/Delta(X),
Re tr_d(Y*X)-h(Y)=Delta(X).                             (BDW3)
```

Moreover `h(Y)` is the value of a finite semidefinite program: its
variables are the Choi matrices of ucp maps
`Theta:C*(G)->M_d`, the constraints
`Theta(u_b)=beta(b)` are linear, and the objective is
`Re tr_d(Y*Theta(u_x))`. Thus a positive selector gap is exactly a finite
complete-order separating inequality, not an existential failure hidden in
an unbounded Stinespring space.

For the authenticated Iwahori sequence, write

```text
G_n=A_(N_n),  B_n=B_(N_n),  beta=beta_n,  X=X_n,
Delta_n=Delta_(N_n,beta_n)(X_n).
```

Then `Delta_n -> 0` is equivalent to the following bounded-dual
statement: for every fixed `M<infinity` and every sequence `Y_n` with

```text
||Y_n||_(2,d_n)=1,       ||Y_n||_op<=M,
```

one has

```text
[ Re tr_(d_n)(Y_n*X_n)-h_n(Y_n) ]_+ -> 0.              (BDW4)
```

Indeed, failure with `Delta_n>=epsilon` produces witnesses with
`M=2/epsilon` by (BDW3), while any positive dual gap lower-bounds
`Delta_n` by (BDW2).

This is a strictly sharper endpoint than generic LLP, MF, or local
reflexivity. A positive proof must use the Iwahori relations to make every
bounded separator pay in the relative induced matrix range. A negative
proof may exhibit one bounded separator sequence retaining a positive gap.
Neither direction is currently known, so the Iwahori gate and the
nonhyperlinear-group root remain open.

DERIVATION
relative-induced-selector-bounded-dual-proof
