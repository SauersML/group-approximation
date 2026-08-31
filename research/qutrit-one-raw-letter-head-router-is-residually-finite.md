---
rg: 2
id: qutrit-one-raw-letter-head-router-is-residually-finite
kind: claim
title: One raw Leavitt letter in the routed head corner is triangular and residually finite
artifacts:
  - research/qutrit-one-raw-letter-triangular-proof.md
distinct_from:
  qutrit-two-scalar-routers-close-full-leavitt-but-head-packet-stays-finite: that proves every all-scalar Q0-head network remains finite; this inserts the first literal positive or negative Leavitt letter and identifies the resulting infinite but residually finite coefficient group.
  qutrit-third-cell-head-selector-is-h-centralizer-zero: that computes the t1 branch deletion inside the h-fixed qutrit table; this composes it with the complete scalar router and proves the one-letter package still has finite regular approximants.
  depth-mismatched-qutrit-root-bridge-is-residually-finite: that treats a one-variable polynomial chart from a depth mismatch; this identifies the idempotent triangular extension forced by the Jacobson head.
---

Put `q=Q_0=s_1t_1=1-s_0t_0`. For `r in {0,1}`, the negative
one-letter algebra is

```text
A_r^-=F_2<q,t_r>
    isomorphic to F_2<q,t | q^2=q, tq=delta_(r1)t>.      (QRL1)
```

It embeds in `M_2(F_2[x])`. Explicitly, in both cases
`q |-> diag(1,0)`, while

```text
r=0:  t |-> [[0,1],[0,x]],
r=1:  t |-> [[x,0],[1,0]].                              (QRL2)
```

The positive algebras `A_r^+=F_2<q,s_r>` are the
anti-isomorphic mirrors, with `qs=delta_(r1)s`. Hence all four
one-letter algebras are residually finite.

Let `K=GL_28(F_2)` and choose the raw roots

```text
H=x_(c_2,c_1)(q),
T_r=x_(c_3,c_2)(t_r).
```

Then

```text
<K,H,T_r>=EL_28(A_r^-),                                 (QRL3)
```

and this group is residually finite and finitely presented. The same
holds with a positive root and `A_r^+`. Thus adjoining one raw Leavitt
letter really escapes the finite algebra `F_2[q]`, but not the
finite-quotient basin.

The two negative branches give the sharp shortest-word dichotomy

```text
[T_0,H]=1,
[T_1,H]=x_(c_3,c_1)(t_1)=B_1.                           (QRL4)
```

For `E=(1-H)/2`,

```text
E T_0 E=T_0E,
(E T_1 E)^2=F_+=E(1+B_1)/2.                             (QRL5)
```

Thus on `R=e_0+e_1` the exact pre-router energies are

```text
||g_1 E T_0 E R||_2^2=1/9,
||g_1 E T_1 E R||_2^2=1/18.                             (QRL6)
```

The killed branch retains the full head source, but the complete qutrit
router still has

```text
||e_2 g_1T_0ER||_2^2=1/81                               (QRL7)
```

and target capacity `tau(Ee_2)=1/18`. The surviving branch creates the
raw `t_1` return, but its D8 polar has already reduced the source from
`1/9` to `1/18`, exactly the one-complement capacity. Neither branch
gives a Hall excess.

For every finite collection of words in `(QRL3)`, reduction of
`F_2[x]` modulo a sufficiently high power of `x` gives a finite ring
quotient separating all nonidentity words in that collection. The left
regular representations of the resulting finite groups retain the qutrit
atoms, the head, the raw-letter commutator, and the displayed norms.
This is an exact finite-regular absorber, not merely an amenability
argument.

Inside the full group `EL_28(L)`, finite-dimensional representations
kill the head and all raw roots because that group is minimally almost
periodic. The local groups `(QRL3)` show that this collapse cannot be
deduced from any relation using only one raw letter. A viable polar
identity must mix at least one positive and one negative letter in
incompatible root positions while simultaneously coupling the result to
the routed `E` source.
