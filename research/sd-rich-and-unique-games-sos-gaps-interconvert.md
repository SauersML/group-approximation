---
rg: 2
id: sd-rich-and-unique-games-sos-gaps-interconvert
kind: claim
title: Algorithms and degree-k SoS integrality gaps for unique games and for admissible-design rich 2-to-1 games interconvert
distinct_from:
  rich-2to1-conjecture-is-equivalent-to-ugc: that is the conjecture-level equivalence of NP-hardness statements; this converts gap instances, pseudo-distributions at matched SoS degree, and algorithms in both directions with explicit parameters.
  admissible-pairing-designs-leak-no-easy-feature: that concerns what the noise test can certify on admissible designs; this concerns what algorithms and SoS relaxations can do on them.
artifacts:
  - research/artifacts/unique-games-sos-algorithms-and-gaps-source-2026-09-12.md
---

**ESTABLISHED.** Two polynomial-time reductions, both acting on labels by linear
maps, so pseudo-distributions transfer at the same degree `k >= 4`.

**(a) Right merging, UG to fully rich 2-to-1.** Let `U` be a unique game with
alphabet `[2k]`. Build `Psi(U)`: right vertices are the pairs `(v,sigma)` with
`sigma` ranging over all 2-to-1 maps `[2k] -> [k]`, and each edge carries the
constraint `sigma o phi_(uv)`. Then

```text
val(U) <= val(Psi(U)) <= 2 val(U),
```

and every left vertex sees the uniform distribution on all pairings, which is
admissible. A degree-`k` SoS gap for `Gap-UG[1-eta, eta']` gives one for
`Gap-2-to-1[1-eta, 2 eta']` on fully rich instances.

**(b) The noise test, admissible 2-to-1 to UG.** For admissible-design instances
in the transfer regime, `R_(rho,m)` maps value `>= 1-eta` to
`>= (1-3epsilon)(1-2eta)`, and value `<= eta(epsilon)` to `<= epsilon`. Pseudo-values
obey the same completeness bound, so degree-`k` gaps transfer.

**Algorithmic consequence.** Both reductions blow instances up by constant
factors. So an algorithm, SoS or otherwise, distinguishing near-1 from near-0 on
admissible-design 2-to-1 instances is an algorithm for `Gap-UG`, and would refute
UGC itself, not just this route. Conversely, every UG algorithm, such as the
subexponential one of Arora--Barak--Steurer, applies to them through `R`. An SoS
gap on admissible designs at degree `k` is an SoS gap for UG at degree `k`.

The admissible-design structure is local to left vertices and leaves the
constraint graph unrestricted. So it gives no handle that the structured-graph
algorithms need: certified small-set expansion (BBKSS) or global
hypercontractivity (Bafna--Minzer). The algorithmic question on admissible
designs is the UG question.

DERIVATION sd-rich-unique-games-gap-interconversion-proof
