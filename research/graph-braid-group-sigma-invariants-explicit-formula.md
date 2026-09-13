---
rg: 2
id: graph-braid-group-sigma-invariants-explicit-formula
kind: claim
title: "Every BNSR invariant of every graph braid group has an explicit graph-theoretic criterion"
distinct_from:
  zaremsky-1-08-bnsr-invariants-of-graph-braid-groups: that claim is Zaremsky's question; this is the answer claim, the explicit criterion itself.
---

For every finite connected graph `Γ`, every `n ≥ 1`, every `m ≥ 1` and every
nonzero character `χ: B_nΓ → ℝ`, membership `[χ] ∈ Σ^m(B_nΓ)` is decided by
an explicit criterion on the data (`Γ`, `n`, `χ`). The criterion is stated in
terms of the values of `χ` on the hyperplane classes of Abrams' cube complex
`UD_nΓ`, and connectivity of finite flag complexes of particle moves built
from those values.

Not established. It becomes established once an artifact states the
criterion and proves both directions for all `Γ` and `n`.

## Attempts

- 2026-09-13 (z1-08-graph-braid): Bestvina–Brady / Bux–Gonzalez Morse theory
  on the universal cover of `UD_nΓ`. The sufficient direction holds for
  affine characters: `(m−1)`-connected ascending links give `Σ^m`. What is
  missing is the converse, i.e. that a non-`(m−1)`-connected ascending link
  forces `[χ] ∉ Σ^m`. For RAAGs this converse is Meier–Meinert–VanWyk. For
  `UD_nΓ` the vertex links are not joins, so their proof does not transfer
  directly.
