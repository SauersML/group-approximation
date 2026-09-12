---
rg: 2
id: injective-automata-restrict-to-schreier-graph-automata
kind: claim
title: An injective automaton maps the configurations fixed by any subgroup onto their image as a graph automaton on the Schreier graph
distinct_from:
  co-amenable-fixed-configurations-lie-in-injective-images: that asks when the fixed configurations of a co-amenable subgroup lie in the image; this is the exact restriction for every subgroup, which turns that question into surjectivity of one graph automaton.
  table-groups-are-memory-holonomy-groups: that computes the group on which a strict design lives; this restricts a pair to the coset space of any subgroup of the host, where no group structure remains.
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

**ESTABLISHED** by `schreier-graph-restriction-proof`.

Let `tau` and `sigma` be cellular automata over a group `G` with memories `M`, `N`, rules `mu`, `nu`,
and `sigma tau = id`. Put `X = tau(A^G)`. For a subgroup `H`, let `Fix_H` be the configurations constant
on the right cosets `Hg`, and let `S = H\G` carry the right action `(Hg).k = Hgk`.

1. `tau(Fix_H) = X cap Fix_H`.
2. Identifying `Fix_H` with `A^S`, `tau` acts as `tau_S(y)(v) = mu((y(v.m))_m)` and `sigma` as
   `sigma_S(y)(v) = nu((y(v.n))_n)`, with `sigma_S tau_S = id`.
3. `Fix_H` lies in `X` exactly when `tau_S` is surjective, and exactly when `sigma_S` is injective.
4. For normal `H`, `tau_S` is the automaton over `G/H` with memory `MH/H`. So `Fix_H` lies in `X`
   whenever `G/H` is surjunctive.

**Filter.** When `Fix_H` lies in `X`, every Garden of Eden pattern of `tau` on a finite set `E` takes
different values at some `e, e'` in `E` with `e' e^-1` in `H`. The same holds for every conjugate of `H`.

Proof: Section 1 of the artifact.
