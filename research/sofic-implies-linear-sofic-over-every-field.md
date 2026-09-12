---
rg: 2
id: sofic-implies-linear-sofic-over-every-field
kind: claim
title: Sofic groups are linear sofic over every field
distinct_from:
  linear-soficity-recognition-has-a-pi2-upper-bound: that computes the arithmetical complexity of linear soficity and mentions this inclusion in passing; this is the inclusion itself, proved over an arbitrary field.
  growing-rank-decoder-is-linear-soficity: that identifies faithful growing coefficient decoders with algebra linear soficity; this is the group-level inclusion of sofic groups into the linear sofic class.
---

ESTABLISHED.  For every field `F` and countable group `G`: if `G` is sofic,
then `G` is `F`-linear sofic, i.e. there is an injective homomorphism

```text
G -> prod_(k->omega) GL_(n_k)(F) / d_omega,     d(a,b) = rank(a-b)/n.
```

Over `F = C` this is Arzhantseva--Paunescu, arXiv:1212.6780, Proposition 4.5
("Sofic groups are linear sofic").  Their proof uses permutation matrices and
the kernel of `A_p - I`; that kernel is the space of vectors constant on the
cycles of `p` over every field, so the same proof works verbatim over `F`.
See [[sofic-implies-linear-sofic-over-every-field-proof]].
