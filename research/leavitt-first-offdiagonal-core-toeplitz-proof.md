---
rg: 2
id: leavitt-first-offdiagonal-core-toeplitz-proof
kind: route
title: Use the Jacobson Toeplitz cover and finite-root direct finiteness
target: leavitt-first-offdiagonal-core-is-marked-non-lef
requires:
  - leavitt-first-offdiagonal-packet-breaks-locally-finite-amalgam
  - toeplitz-defect-needs-square-decoding
---

Write `s=s_0`, `t=t_0`, and `q=1-st=s_1t_1`.  Let

```text
J=F_2<S,T | TS=1>,       Gamma_T=St_5(J),
w_T=x_13(1-ST).
```

The assignment `S->s`, `T->t` is a unital ring homomorphism `J->R`.
Entrywise elementary matrices give a homomorphism

```text
pi:Gamma_T -> G.
```

Constant Weyl words move the two given roots to every root position, root
addition supplies sums, and

```text
[x_ab(r),x_bc(r')]=x_ac(rr')
```

with spare indices supplies products.  Therefore the image of `pi` is the
elementary subgroup over the image of `J`, and in particular
`pi(w_T)=z`.  This is nonidentity because `q!=0`: indeed
`t_1 q s_1=1`.

## Exact finite-dimensional collapse

Let `rho:Gamma_T->U(d)` be a finite-dimensional unitary representation.
Each root subgroup is an elementary abelian `2`-group.  Its commuting
self-adjoint involutions generate a finite subgroup of `U(d)`.  Intersect
the additive kernels of `rho` on the twenty root positions and call the
result `B<=J`.  Then `B` has finite additive index.  Put `I=JBJ`; since
`B<=I`, the ring `J/I` is finite.

Steinberg commutators through two spare indices show

```text
x_ab(I)<=ker(rho)             for every a!=b.             (FNP1)
```

In the finite ring `J/I`, the images of `T,S` satisfy `TS=1`.  A finite ring
is directly finite, so `ST=1` as well.  Hence `1-ST in I`, and `(FNP1)`
gives

```text
rho(w_T)=1.                                                (FNP2)
```

The ring `J` is finitely presented.  The finite-presentation theorem for
rank-at-least-four Steinberg groups over finitely presented associative
rings therefore makes `Gamma_T` finitely presented.

## From the cover to a finite LEF obstruction

We use the following elementary marked-cover lemma.  Suppose a finitely
presented group `Gamma=<X|Rel>` maps to a group `H`, a word `w` maps to a
nonidentity element, and every homomorphism from `Gamma` to a finite group
kills `w`.  Then `H` is not LEF.  Indeed, take the finite subset of `H`
containing the images of all prefixes of the relators in `Rel`, all prefixes
of `w`, their required successive products, and `1`.  An injective partial
homomorphism of this table into a finite group assigns elements to `X`
satisfying every relator exactly, hence extends to a homomorphism from
`Gamma`; the prefixes of `w` make its value nonidentity, a contradiction.

Apply the lemma to `pi:Gamma_T->G`, `(FNP2)`, and `pi(w_T)=z!=1`.  This proves
the marked non-LEF assertion.

## Why finite path and cyclic truncations cannot repair the packet

The obstruction is already visible in the four-element coefficient table

```text
TS=1,                 P=ST,                 Q=1-P.       (FNP2a)
```

In a finite path model, forward and backward shifts can retain a nonzero
endpoint projection `Q`, but the opposite endpoint makes `TS!=1`.  Closing
the path into a cycle repairs `TS=1`; the forward shift is then invertible,
so direct finiteness gives `ST=1` and `Q=0`.  The same dichotomy holds in
every finite unital coefficient ring, independently of the chosen path or
cycle realization.

This coefficient observation alone would not rule out a nonlinear finite
group model.  The finitely presented cover `Gamma_T` is what makes it a
genuine group-table obstruction: its finite presentation compiles root
addition, the spare-index multiplication commutators, and `(FNP2a)` into
one fixed finite ordinary-word table.  The marked-cover lemma then says that
every finite partial group model of that table kills the image of `Q`.
Thus allowing the truncation length to depend on the requested table does
not produce a marked LEF model of `G`.

## Exact Toeplitz normal form

For completeness, put `S_D=<D,s,t><=R`, `A=qDq`, and

```text
e_mn=s^m q t^n.
```

The equations `tq=0`, `qs=0`, and `ts=1` give

```text
(s^m a t^n)(s^k b t^l)=delta_(n,k) s^m(ab)t^l
```

after refining unequal indices in the usual finitary-matrix normal form.
Thus the span `K` of these terms is `M_fin(A)`.  Evaluation of a locally
constant diagonal function at the fixed ray `0^infinity`, together with

```text
s -> zeta,             t -> zeta^(-1),
```

defines the symbol map

```text
0 -> K -> S_D -> F_2[zeta,zeta^(-1)] -> 0.              (FNP3)
```

Every diagonal function is constant on a sufficiently deep zero cylinder;
subtracting that constant leaves a finite sum of the displayed matrix
terms.  Moving all `t` letters to the right using `ts=1` proves both the
normal form and exactness of `(FNP3)`.

The ring `A` is locally finite, hence so is `K`.  Therefore the kernel of

```text
EL_5(S_D)->EL_5(F_2[zeta,zeta^(-1)])
```

is locally finite: a finite set of congruence matrices uses only one finite
matrix corner over one finite subring of `A`.  The quotient is residually
finite by evaluating Laurent coefficients in finite extensions of `F_2`.

Finally, the same root-addition, Weyl, and spare-index commutator argument
used above gives

```text
<Lambda,u,v>=EL_5(S_D).
```

This identifies the prefix-shift enlargement exactly.  The exact
finite-table obstruction comes from the finitely presented subring `J`,
not from failure of the Toeplitz symbol normal form.
