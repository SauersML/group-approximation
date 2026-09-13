---
rg: 2
id: graph-braid-ascending-matching-complex-criterion-is-exact
kind: claim
title: "Membership in Sigma^m(B_n Gamma) forces an affine representative with (m-1)-connected ascending matching complexes"
distinct_from:
  graph-braid-ascending-matching-complexes-give-sigma: that claim is the established sufficient direction; this is the open converse that would make the matching-complex criterion exact
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part2.md
---

If `[χ] ∈ Σ^m(B_nΓ)`, then `χ = χ_c` for a hyperplane-affine `c` such that
every ascending move graph `B↑_c(S)` has an `(m−1)`-connected matching
complex. Horizontal classes (`c = 0`) are allowed, with Bux–Gonzalez-style
horizontal links.

## Attempts

- 2026-09-13 (z1-08-graph-braid): a Meier–Meinert–VanWyk-type converse. A
  non-`(m−1)`-connected ascending link should give a persistent class in the
  superlevel filtration. For RAAGs the proof uses the join structure of links
  and retractions onto special subgroups. For `UD_nΓ` the links are matching
  complexes and not joins, which blocks that proof. Candidate replacements:
  retractions of `B_nΓ` onto braid groups of subgraphs (park particles), or
  local-to-global homology arguments in the style of Witzel–Zaremsky
  arXiv:1501.06682. Constraint: by Theorem E (part 1), when
  `e(UD_nΓ) ≠ 0` no antipodal pair lies in `Σ^d` for `d = min(n, k(Γ))`.
