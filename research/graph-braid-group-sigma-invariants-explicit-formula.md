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
- 2026-09-13 (z1-08-graph-braid), landed pieces, all unreviewed:
  - established: `graph-braid-ascending-matching-complexes-give-sigma` (the
    sufficient criterion; vertex links of `UD_nΓ` are matching complexes of
    move graphs);
  - established: `graph-braid-nonzero-euler-characteristic-sigma-asymmetric`
    (no antipodal pair in `Σ^m` for `m ≥ min(n, k(Γ))` when
    `e(UD_nΓ) ≠ 0`);
  - established: `two-strand-braid-groups-of-k5-and-k33-have-empty-sigma`;
  - open inputs of the route `graph-braid-sigma-formula-via-matching-criterion`:
    `graph-braid-characters-are-hyperplane-affine`,
    `graph-braid-ascending-matching-complex-criterion-is-exact`,
    `graph-braid-matching-complex-connectivity-explicit`.
  Next: the tree braid groups that are RAAGs (Farley–Sabalka,
  arXiv:math/0602444: `B_nT` is a RAAG iff `T` is linear or `n < 4`), where
  Meier–Meinert–VanWyk give the complete answer once the defining graph is
  explicit.
