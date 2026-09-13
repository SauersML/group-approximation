---
rg: 2
id: thompson-f-hyperlinear-iff-relator-system-hs-unstable-proof
kind: route
title: Trace characters of HS almost-representations of F are regular plus abelian, and Z^2 is HS-stable
target: thompson-f-hyperlinear-iff-relator-system-hs-unstable
requires:
  - thompson-f-character-simplex
  - chordal-abelian-graph-products-hs-stable
artifacts:
  - research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md
---

Full proof: artifact, Section 5, which follows Sections 2--3 with traces in place of fixed points.
- **Character.** `chi(g) = lim_omega tr(pi_n(g))` is a character, so by `thompson-f-character-simplex`
  `chi = t tau_reg + (1-t) chi_ab`, and `chi = 1 - t` on `F' \ {e}`.
- **`1 => 3`.** If some unitary almost-solutions keep `||UW - WU||_2 >= epsilon`, then
  `Re chi([a,b]) <= 1 - epsilon^2/2`, so `t > 0`. Then `pi^(⊗ m) ⊗ (lambda_((Z/N)^2) o ab)` has HS defect
  at most `m` times larger and trace tending to `0` off `e`, so `F` is hyperlinear.
- **`3 => 2`.** Almost-commuting unitaries are near commuting ones in the same dimension, because
  `Z^2 = A(edge)` is a chordal RAAG (`chordal-abelian-graph-products-hs-stable`), and commuting pairs
  solve the relators.
- **`2 => 1`.** Separation gives `tr(pi_n([a,b])) -> 0`, while stability gives `pi_n([a,b])` near `1`.
