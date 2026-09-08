---
rg: 2
id: relative-equality-piecewise-injections-are-surjective
kind: claim
title: A finite relative-equality program cannot inject a tuple domain into a proper part of itself
distinct_from:
  certificate-controlled-routing-is-surjunctive: that concerns a data-routing cellular automaton over a certificate full shift; this concerns arbitrary finite-dimensional tuple domains and conditional coordinate translations, with no certificate background.
---

Fix any group G, a finite integer n>=1, and a finite set of control
states C. Let X be a subset of C x G^n definable by a finite Boolean
combination of control-state conditions and relative equalities

    g_i^(-1) g_j = s,                 s in G.

Suppose F:X->X is a map given on finitely many such definable pieces
by instructions of the form

    (c,g_1,...,g_n) -> (d,g_1 h_1,...,g_n h_n),

where d and the h_i are constants on the piece. If F is injective,
then F is surjective. The statement permits arbitrary group elements
as constants and places no amenability or approximation condition on G.

Finite programs can use any finite nesting of these tests, since their
branches reduce to a finite Boolean partition. The theorem does not
cover unbounded loops that keep testing new relative positions or an
unbounded number of registers. In particular, it excludes a strict
Hilbert-hotel map produced by a bounded relative-equality computation;
it does not assert that arbitrary programs over G are surjunctive.
