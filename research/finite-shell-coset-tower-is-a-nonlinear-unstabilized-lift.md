---
rg: 2
id: finite-shell-coset-tower-is-a-nonlinear-unstabilized-lift
kind: claim
title: The finite-shell coset tower exists after one regular stabilization but not from character data
distinct_from:
  stabilizer-orbit-commutators-have-a-kesten-chart-carrier: that constructs one explicit unstabilized D-invariant spectral projection and finds a large overlap floor; this classifies the abstract coset-tower target and gives its exact stabilized model.
  sl3-one-over-forty-two-packet-is-external-or-folded: that rules out identifying an external finite packet atom with the native arithmetic carrier by the existing fold syntax; this shows exactly why the external packet nevertheless solves the operator problem after stabilization.
  finite-group-selector-induction-barrier: that supplies unwanted selector characters in arbitrary finite-packet representations; this records the positive quasi-regular module already present in the native Koopman representation and isolates projection multiplication as the missing datum.
---

**ESTABLISHED REDUCTION AND STABILIZED MODEL; THE UNSTABILIZED LIFT IS
OPEN.**  Let

```text
N=core_C(D),       Q=C/N,       H=D/N,       [Q:H]=42,
M=L(W_S),
```

where `W_S` is the graph-product lamp group on the finite 42-point shell and
`alpha:Q->Aut(M)` is the shell-permutation action.

An exact `D`-fundamental projection in `M` is exactly a unital equivariant
embedding

```text
Phi:l_infinity(Q/H)->M.                               (FST1)
```

Indeed, from such an embedding take `E=Phi(1_H)`.  Conversely, if

```text
alpha_h(E)=E                    (h in H),
alpha_g(E) alpha_k(E)=0         (gH!=kH),
sum_(gH in Q/H) alpha_g(E)=1,                         (FST2)
```

then the translates of `E` define `(FST1)`.  Necessarily
`tau(E)=1/42`.

## The exact stabilized tower

Let `pi` be the quasi-regular permutation representation on
`ell^2(Q/H)` and put

```text
M_tilde=M tensor B(ell^2(Q/H)),
beta_g=alpha_g tensor Ad(pi(g)).                       (FST3)
```

Then

```text
E_tilde=1 tensor |delta_H><delta_H|                   (FST4)
```

is fixed by `H`, its 42 coset translates are pairwise orthogonal, and they
sum to one.  Thus the desired tower has no dimension, trace, or finite-group
representation obstruction after one fixed 42-dimensional inner
stabilization.

The same conclusion holds on any nonzero `alpha`-invariant carrier: tensor
that carrier with `(FST4)`.  Hence a proposed trace or subfactor-index
obstruction must distinguish the original action from its inner regular
stabilization; index 42 alone cannot do so.

## The linear obstruction is also absent before stabilization

Let `a=hC` be the distinguished shell vertex.  In
`L^2(M)=ell^2(W_S)`, the 42 vectors

```text
lambda(c_(ga)),             gH in Q/H,                (FST5)
```

are orthonormal and are permuted quasi-regularly by `Q`; the stabilizer of
the first vector is exactly `H`.  Therefore the Koopman representation of
the **unamplified** action already contains `ell^2(Q/H)`.  In particular the
coefficient/character condition forced by a tower is present.  Replacing
the group-unitary vector in `(FST5)` by a projection of trace `1/42` while
preserving the multiplication laws `(FST2)` is the genuinely nonlinear
step.

## Exact scope for finite syntax

A finite role packet carrying `pi` realizes `(FST3)--(FST4)` in one chosen
block, but its multiplication table does not identify that block in every
representation.  Induction supplies the other packet types, and tensoring
the native model with them preserves every separate actor and graph-product
relation.  Thus a bare finite packet proves only stabilized existence.  To
use it in the native compiler one still needs an ordinary-word coupling
that authenticates the quasi-regular rank-one atom on the marked native
carrier.  That is precisely the external-or-folded seam, not a consequence
of finite-group Rokhlin terminology.

No nonexistence statement for `(FST1)` follows from the Kesten floor:
`kesten-chart-carriers-have-25-over-42-gram-floor` rules
out one particular spectral projection, not all projections in `M^H`.
Likewise, general outer-action Rokhlin results typically produce approximate
or ultrapower towers under additional hypotheses; they do not by themselves
supply the exact projection `(FST2)` in this specified nonamenable factor.
The exact residual is therefore the unstabilized equivariant embedding
`(FST1)`.

Even `(FST1)` would not by itself authenticate a nonlinear Fano payload.
`coset-tower-hybrid-reflection-pays-exact-payload-leakage` proves that the
block compression `R=sum_iE_iA_iE_i` satisfies

```text
tau(1-R^2)=1/2 sum_i||[E_i,A_i]||_2^2.
```

Hence a sharp tower must additionally reduce the assigned payload rows.
The stabilized tower has this property because its atoms are external
matrix coordinates.  Inside `L(W_S)`, requiring reduction of every native
shell lamp would put every tower atom in the center and is impossible.
Accordingly the unstabilized tower and the payload-authenticating
commuting-square are two separate gates; solving the former alone does not
solve the Fano hybrid-reflection problem.
