---
rg: 2
id: finite-injective-positive-charge-automata-are-surjective
kind: claim
title: A finite-alphabet cellular automaton conserving a strictly positive charge and injective on finite configurations is surjective over every group
distinct_from:
  finite-injective-conservative-binary-automata-are-surjective: that treats one binary particle per occupied site; this encodes general states by complete colored token packets and allows any strictly positive real charge away from a unique zero symbol.
artifacts:
  - research/artifacts/conservative-ca-literature-and-trace-scope-2026-09-07.md
---

Let G be any group and A a finite alphabet with distinguished symbol 0.
Let w:A->R satisfy

    w(0)=0,                 w(a)>0 for every a!=0.

Let tau:A^G->A^G be a cellular automaton fixing the all-zero
configuration. A configuration is finite if it equals 0 outside a
finite set. Suppose:

1. For every finite x, sum_g w(tau(x)(g))=sum_g w(x(g)).
2. Tau is injective on the set of finite configurations.

Then tau is bijective on the finite configurations of each prescribed
total charge and is surjective on A^G. In particular, a globally
injective CA with such a conserved charge is surjective over every G.
The conclusion does not assert global injectivity from the weaker
finite-configuration hypothesis.

For positive integer charges, replace an occupied state a by the complete
packet of w(a) distinct tokens colored (a,1),...,(a,w(a)). At fixed total
charge there are finitely many local interacting-cluster types. Weighted
Hall matchings lift tau to an injective, finitely defined map on ordered
token tuples. The valid-packet condition is defined by finitely many
coordinate equalities and finite colors. Stable finiteness of the
associated collision-operator corner forces that map onto.

For positive real charges, the integer count-difference vectors of finite
executions span a rational subspace. Its annihilator contains w and hence
contains a strictly positive rational vector. Scaling gives a conserved
positive integer charge, reducing to the token construction.

The unique zero-charge symbol is a substantive hypothesis. No claim is
made for several zero-charge states, signed charges, or automata without
such conservation. In particular, this result does not settle unrestricted
Gottschalk surjunctivity or universal Kaplansky direct finiteness.
