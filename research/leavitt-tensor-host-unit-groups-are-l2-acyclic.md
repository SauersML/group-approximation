---
rg: 2
id: leavitt-tensor-host-unit-groups-are-l2-acyclic
kind: claim
title: For every simple unital F_2-algebra B, the unit group of B ⊗ L_(F_2)(1,2) is L²-acyclic
distinct_from:
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that gives integral acyclicity, Steinberg comparison and finite presentation over B ⊗ L under vanishing of K-theory; this is L²-acyclicity over the same rings with no K-theory hypothesis.
  binary-leavitt-unit-group-is-l2-acyclic: that is the case B = F_2; this covers every simple B, including the finitely presented simple group (L ⊗ L)^x.
---

**ESTABLISHED (proved on paper, unreviewed).** Let `B` be a simple unital `F_2`-algebra,
`L = L_(F_2)(1,2)` and `S = B ⊗ L`. Then `β_n^(2)(S^x) = 0` for every `n >= 0`.

In particular `(L ⊗ L)^x` is L²-acyclic. It is finitely presented, simple and integrally
acyclic (`leavitt-square-unit-group-is-fp-simple-and-acyclic`), and nonsofic, because
`a ↦ 1 ⊗ a` embeds `L^x` in it.

Route: `leavitt-tensor-host-unit-groups-l2-acyclic-proof`.
