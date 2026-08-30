---
rg: 2
id: mikhailova-left-right-soficity-is-one-color-code
kind: claim
title: Mikhailova left-right soficity is exactly one asymptotically commuting color code
distinct_from:
  mikhailova-left-right-action-current-frontier: that records the literature boundary and leaves the positive-density chart condition in its general form; this collapses that condition to one base coloring with a two-valued stabilizer coefficient.
  mihailova-actor-liftable-ce-forces-q-hyperlinear: that assumes exact projective actor lifts in matrices; this is an exact permutation-ultraproduct criterion with no liftability or stability assumption.
  mihailova-left-right-local-models-do-not-see-q: that concerns arbitrary finite metric patches; this identifies the additional common-color Hamming datum those patches lack.
---

Let `q:F_m->H` be onto, put `G=F_m x F_m`, and let

```text
M_H={(u,v) in G:q(u)=q(v)}.
```

For the left-right action

```text
G acts on H,        (u,v).h=q(u)h q(v)^(-1),          (MCC1)
```

the following are equivalent.

1. The action `(MCC1)` is sofic in the sense of
   Gao--Kunnawalkam Elayavalli--Patchell.
2. For some universal sofic group `S_U`, its universal color space
   `X_U`, and universal action `S_U:S_U acts on X_U`, there are a
   homomorphism `Phi:G->S_U` and one color point `c in X_U` such that

```text
d_U(c,S_U(Phi(g))c)=0   for g in M_H,
d_U(c,S_U(Phi(g))c)=1   for g notin M_H.               (MCC2)
```

Equivalently, after choosing representatives, there are exact homomorphisms

```text
sigma_n,tau_n:F_m->Sym(A_n)
```

whose images asymptotically commute, and colorings
`c_n:A_n->N`, such that for every `u,v in F_m`,

```text
|{a in A_n:
    c_n((sigma_n(u)tau_n(v))^(-1)a)=c_n(a)}| / |A_n|
       -> 1_(q(u)=q(v)).                                (MCC3)
```

Thus the open problem is not the construction of two separate coordinate
charts.  It is the construction of one common color code whose agreement
coefficient recognizes exactly equality in `H`, while the two free-factor
permutation representations commute only asymptotically.

There is a sharp quotient-detection consequence.  If a witness to `(MCC2)`
also satisfies

```text
Phi(n,1)=1  for every n in ker(q),                       (MCC4)
```

then `u |-> Phi(u,1)` factors to a sofic embedding of `H`: equation
`(MCC2)` makes every nonidentity quotient element nontrivial.  Hence for
the repository's nonsofic `H`, every hypothetical witness must fail
`(MCC4)`; some kernel word remains nontrivial in the permutation
ultraproduct even though it fixes the color point.  The same applies to the
right coordinate.

This is the exact nonstable gap.  Promoting color-point invariance to
identity of the underlying permutations would solve the action negatively
for the fixed nonsofic quotient, but neither GKP soficity nor the separate
free actions provide that promotion.

DERIVATION
[[mikhailova-one-color-code-proof]]
