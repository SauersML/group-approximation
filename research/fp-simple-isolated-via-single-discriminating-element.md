---
rg: 2
id: fp-simple-isolated-via-single-discriminating-element
kind: route
title: One nontrivial element discriminates a simple group, and finite presentation then gives isolation by the Cornulier--Guyot--Pitsch characterization
target: fp-simple-groups-are-isolated
requires: []
---

Notation and imported statements as in the target.

Let `S` be finitely presented and simple, so `S ≠ 1` and its only normal
subgroups are `1` and `S`. Pick `s ∈ S − {1}` and put `F = {s}`. A non-trivial
normal subgroup of `S` is `S` itself, which contains `s`. So `F` is a finite
discriminating subset and `S` is finitely discriminable. Since `S` is finitely
presented, the CGP Proposition (lines 554–557) makes `S` isolated.
