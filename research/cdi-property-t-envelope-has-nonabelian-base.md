---
rg: 2
id: cdi-property-t-envelope-has-nonabelian-base
kind: claim
title: The Chifan-Drimbe-Ioana universal property-T envelope does not supply an algebraic compact-abelian base
distinct_from:
  non-ce-property-t-equivalence-relation-exists: that correctly uses the source to obtain a property-T relation-factor envelope; this audits why the same source does not compile that envelope into a group factor.
  algebraic-compact-action-envelope-for-non-ce-relation: that remains the missing construction; this identifies the exact nonabelian-base and cocycle obstruction in the cited universal envelope.
---

Chifan--Drimbe--Ioana's embedding-universality theorem does **not** construct
the target as a Haar compact-abelian algebraic crossed product.  For an input
tracial algebra `M`, their proof first forms a nonabelian factor `M_tilde`
containing `M` and then constructs

```text
Q = M_tilde^C rtimes_(beta,w) C,
```

where `(beta,w)` is a cocycle action.  Thus the canonical base is a tensor
power of the input factor, not `L^infinity(K,Haar)`, and the action is twisted.
Their paper explicitly states that it is open whether group II1 factors form
an embedding-universal family.  Consequently neither their Theorem A nor its
property-`(T)` relation analogue supplies `(AAE1)` or `(ACAE1)`; turning this
particular construction into an algebraic compact-action envelope would
require an additional theorem not present in the source.

There is nevertheless a precise positive residue.  Choose for `H` a
cocompact lattice in `Sp(n,1)`, `n>=2`.  Such `H` is a finitely generated
linear (hence residually finite and hyperlinear), hyperbolic property-`(T)`
group.  Applied to the fixed non-CE input, Theorem A(1) gives a representation
`pi:H -> U(Q)` with `pi(H)''=Q` and `Q` non-CE.  Therefore
`chi(h)=tau_Q(pi(h))` is a non-CE character on a tame hyperlinear property-`(T)`
group.  This is the same exact firewall as `non-ce-trace-on-sofic-racg`:
generation by group unitaries does not identify `chi` with the canonical
delta trace.  The missing operation is canonical-trace promotion, not merely
finding a group representation which generates the envelope.

Primary source: Chifan--Drimbe--Ioana,
[*Embedding universality for II1 factors with property (T)*](https://arxiv.org/abs/2205.07442),
Remark 1.1 and the proof of Theorem A(1), especially Proposition 3.8 as used in
Section 5.1.
