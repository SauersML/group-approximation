---
rg: 2
id: qutrit-head-exactification-carrier-proof
kind: route
title: Exactify the finite head envelope and compute the qutrit carrier energies
target: qutrit-head-exactification-halves-every-carrier
requires:
  - qutrit-head-only-overlap-envelope-is-finite
  - qutrit-scalar-exactification-has-no-central-index
  - binary-jacobson-first-alternating-ts-closure-relation
---

Evaluation at the two values of the idempotent gives

```text
A_Q -> F_2 x F_2,             a+bQ |-> (a,a+b).
```

Consequently

```text
B=EL_28(A_Q)=K x K.
```

The constant matrices give the diagonal subgroup
`Delta K={(k,k):k in K}`, while

```text
h=x_12(Q)=(1,u),              u=x_12(1) in K.            (QHE4)
```

The group `K=PSL_28(F_2)` is simple. Conjugating `h` by
`Delta K` produces `(1,kuk^(-1))`; the normal closure of the
nonidentity element `u` is all of the second factor. Hence
`<Delta K,h>` contains `1 x K`, and multiplication by the diagonal
copy gives all of `K x K`. This proves `B=<K,h>`.

Now let trace-preserving microstates of an ambient group be defined on
increasing finite sets containing `B`. Finite-group
Hilbert--Schmidt stability, with an `o(d_l)` stabilization if necessary,
perturbs the restriction to exact representations
`sigma_l:B->U(D_l)`. Their normalized characters converge to the regular
character of `B`.

For any projection `p in C[Delta K]`, put

```text
E_l=(1-sigma_l(h))/2,          p_l=sigma_l(p).
```

The element `h` is an involution, so `E_l` is a projection.
The exact identity

```text
||E_l p_l||_2^2
 = tr_(D_l)(p_l E_l p_l)
 = (1/2)(tr_(D_l)(p_l)-tr_(D_l)(p_l sigma_l(h)))         (QHE5)
```

reduces the calculation to two canonical traces. Write
`p=sum_k c_k (k,k)`. No group element `(k,k)h=(k,ku)` is the
identity: its first coordinate would force `k=1`, after which its second
coordinate would force `u=1`. Therefore

```text
tau_B(p h)=0,                 tau_B(p)=tau_K(p).          (QHE6)
```

Regular-character convergence in `(QHE5)` proves `(QHE1)`.
The qutrit values

```text
tau_K(q)=1/3,       tau_K(R)=2/9,       tau_K(q-R)=1/9
```

give `(QHE2)`. In particular `tr(E_l)->1/2`, as also follows
directly from the canonical trace-zero condition on the nonidentity
involution `h`. More finely, each of the nine qutrit atoms has
head-surviving squared mass `1/54`; the six selected atoms of `R`
and the three complement atoms retain their exact three-phase bookkeeping.

Conjugation by an actor unitary `U_l` preserves these norms. Set

```text
E_l'=U_l E_l U_l^*,       q_l'=U_l q_l U_l^*,
R_l'=U_l R_l U_l^*.
```

For arbitrary contractions `C_l,D_l`,

```text
||C_l E_l'(q_l'-R_l')D_l||_2
 <= ||E_l'(q_l'-R_l')||_2 -> 1/(3 sqrt(2)),
||U_l E_l R_l||_2 -> 1/3.                               (QHE7)
```

The reverse triangle inequality proves `(QHE3)`. Thus any fixed word
identity or rounded polar relation which makes the first displayed
occurrence converge to the second is quantitatively impossible. By
contrast, two orthogonal target copies have limiting squared capacity
`2(1/18)=1/9`, exactly the source value, so exactification alone cannot
select the forbidden one-branch support graph.

Finally, let `G_0=B * <v>`, with `v` infinite cyclic. Free products
of residually finite groups are residually finite, so finite quotients
which are injective on increasing balls, followed by their left regular
representations, give canonical trace-preserving microstates of `G_0`.
They retain the exact finite group `B`, the trace-zero head involution,
all qutrit projections and phase cancellations, the infinite actor on every
fixed ball, and the exact conjugate finite subgroup `vBv^(-1)`.
Therefore all identities used in `(QHE1)` and bare conjugacy transport
are jointly compatible.

What these models omit is precisely a mixed Jacobson relation. The first
eligible established relation is the alternating closure word

```text
W=[[H c H,k],H z H] z=1,
```

where the separately retained opposite root `k=x_31(1)` exposes
`u_T=x_21(T)`, the raw root `s=x_13(S)`, and
`[u_T,s]=x_23(TS)=x_23(1)`. A successful continuation must compress
that separate `k` occurrence jointly with the raw `SQ` range and prove
the one-branch factorization tested in `(QHE7)`. The finite-head and
free-product calculations neither prove nor assume that missing carrier
identity.
