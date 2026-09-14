---
rg: 2
id: intermediate-growth-groups-have-deficiency-at-most-zero
kind: claim
title: Every finite presentation of a group of intermediate growth has at least as many relators as generators
distinct_from:
  fp-intermediate-growth-witness-exclusions: that collects cover, normal-subgroup, gap and endomorphic-presentation constraints; this excludes positive deficiency through asphericity and Kochloukova's Novikov-ring theorem
  fp-subexponential-growth-forces-sqrt-mod-p-betti-bound: that gives deficiency at most one and a square-root mod-p Betti bound for all subexponential growth; this removes deficiency one for intermediate growth
---

**ESTABLISHED** through `intermediate-growth-deficiency-at-most-zero-proof`.

Let `G` be a finitely generated group of intermediate growth.
1. Suppose `G` has a finite 2-dimensional `K(G,1)` complex `Y` with `χ(Y) = 0`. Then every
   finite-index subgroup of `G` has finite abelianization.
2. `G` has no finite presentation `⟨X | R⟩` with `|X| > |R|`. So a finitely presented group of
   intermediate growth, if one exists, has deficiency at most 0.

No novelty is claimed. The claim assembles imported and landed theorems.

The growth hypothesis is needed:
- `Z² = ⟨a,b | [a,b]⟩` has deficiency one and polynomial growth.
- `BS(1,2) = ⟨a,t | tat⁻¹ = a²⟩` has deficiency one and exponential growth.
