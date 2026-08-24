---
rg: 2
id: wandering-leavitt-corner-reflection-compiler
kind: claim
title: A wandering Leavitt corner internalizes the complete MF reflection of its actor
root: true
artifacts:
  - research/wandering-leavitt-corner-reflection-proof.md
---

Let `U=L_(F_2)(1,2)^x`, let `Q<=U` be countable, and suppose there are
elements `s,t` in the Leavitt algebra such that

```text
t s=1,       p=s t,
```

and the idempotents

```text
p_q=q p q^(-1)                 (q in Q)
```

are pairwise orthogonal.  Then there is a canonical internal embedding

```text
W(Q,p)=U^(Q) semidirectProduct Q <= U,                   (WC1)
```

where `Q` acts regularly on the restricted base.  If
`pi:W(Q,p)->Q` is the quotient map, then

```text
Rad_MF(W(Q,p))=pi^(-1)(Rad_MF(Q)),                       (WC2)
R_MF(W(Q,p)) ~= R_MF(Q).                                (WC3)
```

The theorem identifies the entire outgoing MF representation functor:

```text
Hom(Q,M) ~= Hom(W(Q,p),M)                               (WC4)
```

naturally for every MF group `M`.  For every normal subgroup `N` of
`W(Q,p)`, it also gives the complete semantic-closure formula

```text
cl_MF^(W(Q,p))(N)
  =pi^(-1)(cl_MF^Q(pi(N))).                              (WC5)
```

If `Q` is MF, the radical is exactly the base `U^(Q)`.  If every quotient of
`Q` is MF and `d!=1` normally generates `U`, then the copy of `d` in the
identity coordinate normally generates the radical and

```text
cl_MF^(W(Q,p))(N)=N normalClosure_(W(Q,p))(d),           (WC6)
W(Q,p)/N is MF  iff  d belongs to N.                     (WC7)
```

If `Q` is finitely generated, then `W(Q,p)` is finitely generated.  The same
factorization as `(WC4)` holds for any target class to which every
homomorphism from `U` is trivial.
