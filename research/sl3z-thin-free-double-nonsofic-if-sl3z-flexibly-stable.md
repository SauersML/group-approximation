---
rg: 2
id: sl3z-thin-free-double-nonsofic-if-sl3z-flexibly-stable
kind: claim
title: If SL_3(Z) is flexibly stable, its double over an explicit profinitely dense free subgroup of rank two is a finitely presented nonsofic group
artifacts:
  - research/artifacts/solve-sofic-amalgam-2026-09-13.md
distinct_from:
  sln-z-thin-codense-tau-pair: that supplies the thin co-dense pair and records the unitary HNN endpoint; this is the permutation endpoint for the amalgamated double.
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that is the unitary HNN theorem over a co-dense subgroup, under flexible Hilbert--Schmidt stability; this is the permutation theorem for the amalgamated double, under flexible permutation stability.
  free-group-doubles-over-any-subgroup-are-sofic: that shows every double of a free actor is sofic; this takes the Kazhdan actor SL_3(Z) with a free edge group, where soficity of the double would refute flexible stability.
---

**ESTABLISHED** as an implication. Not independently reviewed; no priority
is claimed.

Let `A = SL_3(Z)`, and let `C = <a,b>` be the free, profinitely dense, rank-two
subgroup given by the displayed matrices of `explicit-sl3-thin-codense-tau-pair`.
Put

```text
D = A *_C A = < two copies of a presentation of SL_3(Z) | i_0(a) = i_1(a), i_0(b) = i_1(b) >.
```

`D` is finitely presented, because `SL_3(Z)` is.

**Theorem.** If `A` is flexibly stable in the sense of Bowen--Burton, then `D`
is not sofic. In particular this holds if `A` is flexibly P-stable in the
sense of Becker--Lubotzky.

- **What folds.** Let `r` be the order-three matrix `(ES3)` of the explicit
  pair node, so `r` is not in `C`. The fold word `w = i_0(r) i_1(r)^(-1)` is
  nontrivial in `D`. Under flexible stability, every asymptotically
  multiplicative model of `D` whose vertex restrictions are sofic
  approximations sends `w` close to the identity.
- **Every `n >= 3`.** The same holds for `SL_n(Z)`, using the four-generated
  free profinitely dense subgroup of `sln-z-thin-codense-tau-pair`.
- **The contrapositive.** A sofic approximation of `D` refutes
  `sl3z-is-flexibly-permutation-stable`.

## Context

- **Bowen--Burton.** Their theorem (arXiv:1906.02172) says that flexible
  stability of `PSL_d(Z)` for some `d >= 5` gives a nonsofic group, a modular
  HNN extension. They need `d >= 5` for an orbit-density bound. Verbatim: "We
  do not know whether the result can be improved to `d in {3,4}`."
- **What is new here.** This claim gives the implication for `SL_3(Z)` and
  `SL_4(Z)`, with a plain double and no orbit-density input. It comes from
  `codense-tau-amalgams-fold-under-flexible-stability`.
- **What it is for.** Nonsofic groups are known unconditionally
  (`openai-leavitt-unit-nonsofic`). The content here is the mechanism, and a
  concrete finitely presented test for flexible stability of `SL_3(Z)`.
- **Consequences under the same hypothesis.** The set action of `A` on `A/C`
  is not sofic. Nor is the HNN extension `<SL_3(Z), t | [t,a] = [t,b] = 1>`,
  which contains `D`.

## Not covered

- **Thin but not profinitely dense edge groups.** Zariski-dense thin subgroups
  whose profinite closure is a proper open subgroup are not handled. They
  would need strong approximation for non-separability and an explicit gap
  statement on proper images. Neither was pinned here.
- **Twisted embeddings.** Take `A *_H A` with `iota_1 = iota_0 o theta`, where
  `theta` does not extend algebraically. The fold theorem then needs a uniform
  gap for the graph subgroup on all finite `A x A`-sets, i.e. arbitrary-modulus
  expansion for Zariski-dense subgroups of `SL_3 x SL_3`. That was not checked.

DERIVATION
sl3z-thin-free-double-nonsofic-from-fold-theorem
