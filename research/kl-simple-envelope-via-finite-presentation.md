---
rg: 2
id: kl-simple-envelope-via-finite-presentation
kind: route
title: Take the counterexample down to a finite presentation, then up into a simple envelope
target: kl-counterexample-can-be-two-generator-simple
requires: [kl-counterexample-can-be-finitely-presented, countable-group-embeds-in-two-generator-simple-group]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

By the first prerequisite take the counterexample `(P, w)` with `P` finitely
presented, hence countable, `deg_t(w) = m != 0`, and `1 != a in P` dying in
`P_w`.  By the second, fix an embedding `P <= S` with `S` two-generator
nonabelian simple, and read `w` in `S * <t>`.

Death is witnessed by the finite identity
`a = prod_j u_j w^{e_j} u_j^{-1}` in `P * <t>`.  That identity is a relation
between elements of `P * <t> <= S * <t>`, so it persists verbatim, and `a`
dies in `S_w`.  It is nontrivial in `S` because the embedding is injective.
Hence `(S, w)` is a counterexample.

## Why the down-step is needed at all

It is not: countability is all the embedding theorem asks, and the
coefficient-subgroup localization already delivers a countable — indeed
finitely generated — counterexample.  The finite-presentation step is kept in
front of it because it is the statement worth having on its own
(`kl-counterexample-can-be-finitely-presented`: a counterexample is finite
input data), and because passing through it makes the chain's two halves
independent — one purely combinatorial, one purely a citation.

## What does not transfer

Nothing about `P` survives except the identity.  The route moves a relation,
not a group, which is exactly why it costs nothing and buys the rigidity of
the simple case.
