---
rg: 2
id: hhg-with-torsion-rips-proof
kind: route
title: A hierarchically hyperbolic group acts properly and cocompactly on a coarsely injective space, and the torsion-allowed orbit criterion applies
target: hierarchically-hyperbolic-groups-have-contractible-rips
requires:
  - hierarchically-hyperbolic-groups-are-coarsely-injective
  - coarsely-injective-groups-with-torsion-have-contractible-rips
---

By the first prerequisite, `H` acts properly and cocompactly by isometries on a coarsely
injective space `(X, σ)` ("every hierarchically hyperbolic group acts properly cocompactly
on a coarsely injective space", Haettel–Hoda–Petyt, as imported). Properness is in the
sense used by the second prerequisite: `{h : hB ∩ B ≠ ∅}` is finite for every ball `B`.

**Cocompact gives cobounded.** Let `K ⊆ X` be compact with `H K = X` and fix `x_0 ∈ X`.
`K` is bounded, so `D = sup_(k ∈ K) σ(k, x_0)` is finite. A point `h k` lies within
`σ(hk, h x_0) = σ(k, x_0) ≤ D` of `h x_0`.

The coarse injectivity constant `δ` in Haettel–Hoda–Petyt's definition ("the
`δ`-neighbourhoods of those balls have nonempty total intersection") gives a point within
`r_i + δ` of every centre `x_i`, which is the form used by the second prerequisite.

Apply `coarsely-injective-groups-with-torsion-have-contractible-rips`. No torsion-freeness
is needed. For every integer `t ≥ ⌈4δ + 4D + 2⌉`, `T_t = {h ≠ 1 : σ(x_0, h x_0) ≤ t}` is a
finite symmetric generating set and `P_1(H, T_t)` is contractible. ∎
