---
rg: 2
id: thompson-v-torsion-centralizers-are-rationally-acyclic
kind: claim
title: Every centralizer of a finite-order element of Thompson's group V is rationally acyclic
distinct_from:
  thompson-v-is-integrally-acyclic: that is the acyclicity of V itself; this extends the rational statement to every torsion centralizer, the input of any delocalized (conjugacy-class-indexed) cohomological invariant.
  braided-thompson-group-bv-is-rationally-acyclic: that is about the braided group bV; this is about centralizers inside the plain group V.
---

**ESTABLISHED** by `thompson-v-torsion-centralizers-are-rationally-acyclic-proof`.

Let `g ∈ V` have finite order and let `C = C_V(g)` be its centralizer. Then

```text
H_k(C; Q) = 0   and   H^k(C; Q) = 0     for every k ≥ 1.
```

The case `g = 1` is `thompson-v-is-integrally-acyclic` tensored with `Q`.

**Why it is recorded.** Delocalized refinements of cohomological obstructions
to matricial stability take their input from `H^(2k)(C_G(g); Q)` for torsion
`g`, one summand per conjugacy class. For `V` every such summand vanishes for
`k ≥ 1`, as does `H^(2k)(V; Q)` itself, the input of
`dadarlat-matricial-stability-obstruction`. So for `V` this whole lane has no
input. It is used in `thompson-v-k-shadow-cannot-detect-mf`, part (iii).
