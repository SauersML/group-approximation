---
rg: 2
id: fpbs-tree-projected-rigid-decorations-strict-thresholds
kind: claim
title: Rigidly decorated tree-projected Cayley graphs of F_n x Z have strict thresholds
distinct_from:
  fpbs-tree-projected-cayley-graphs-strict-thresholds: that is the root for every cyclic-by-free group and every decoration; this is the part of it that no established claim covers, rigid decorations over F_n x Z, to which the root reduces.
  fpbs-tree-projected-rigid-decorations-discrete-automorphisms: that is the obstruction that rigid decorations admit no nonunimodular fibre-preserving symmetry, with a discrete automorphism group for one example; this asks for strict thresholds on the same graphs.
  fpbs-tree-projected-large-rank-strict-thresholds: that settles every decoration when v + 2m sqrt(2n-1) < 2n-1, which for rigid sets needs n >= 19; this asks for every rank, including two.
  fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular: that settles every decoration when the cyclic kernel is not central; this is the central case, where that construction has nothing to exchange.
  fpbs-tree-projected-letter-exchange-nonunimodular: that covers F_n x Z when two decoration sets agree up to translation and reflection; this is the complementary case.
---

**OPEN.** Let `Gamma = F_n x Z` with `n >= 2` and free basis `B`. Let `S` be a
finite symmetric generating set with `pi(S) ⊆ {1} ∪ B ∪ B^(-1)`. Put
`D_s = {k : (s,k) in S}` for `s in B`, and let the vertical part be arbitrary.
Call the decorations *rigid* if the `2n` sets `D_s`, `-D_s` (`s in B`) are pairwise
distinct up to translation. If they are rigid, then

```text
p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)).
```

A set of one or two heights is symmetric up to translation, so rigid decorations
have `|D_s| >= 3` for every letter. The smallest recorded example is
`S_rig = {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}` in `F_2 x Z`.

**Why this is the remaining case.** Route
`fpbs-tree-projected-reduce-to-rigid-decorations` derives
`fpbs-tree-projected-cayley-graphs-strict-thresholds` from this claim and three
established claims:
* non-central kernels: `fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular`;
* a decoration set symmetric up to translation:
  `fpbs-tree-projected-reversible-letter-nonunimodular`;
* two decoration sets agreeing up to translation and reflection:
  `fpbs-tree-projected-letter-exchange-nonunimodular`.

## Attempts

* **Nonunimodular structure.** **Where it dies:**
  `fpbs-tree-projected-rigid-decorations-discrete-automorphisms`. With vertical part
  `{(1,±1)}`, every fibre-preserving automorphism lies in the discrete group
  `Gamma ⋊ Z/2`. For `S_rig` the whole automorphism group is discrete, so
  Hutchcroft arXiv:1711.02590 cannot apply.
* **Twisting (2026-09-16).** The mechanism of
  `fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular` uses a letter acting by
  `-1`, so that both edges of that letter at a vertex carry the same oriented
  shape. **Where it dies:** over `F_n x Z` every letter has one outgoing and one
  incoming edge at each vertex, with shapes `D_s` and `-D_s`, and rigidity forbids
  matching them. The twisted group contains `ker chi ≅ Z x F_(2n-1)` with index 2,
  but its tree-projected Cayley graphs are not Cayley graphs of `F_m x Z`, and no
  comparison of thresholds between the two kinds of graph is known.
* **Large rank.** `fpbs-tree-projected-large-rank-strict-thresholds` needs
  `v + 2m sqrt(2n-1) < 2n-1`. Rigid sets have `m >= 3`, so this needs `n >= 19`
  (with `v = 0`) or `n >= 21` (with `v = 2`). **Where it stops:** rank two is far
  out of reach.
* **Oriented second moment and non-backtracking resolvent (2026-09-17).**
  `fpbs-tree-projected-oriented-second-moment-thresholds` replaces both crude bounds:
  * `p_c <= [(2n-1)m - (m-1)^2/((2n-2)m^2+m-1)]^(-1)`, by Paley–Zygmund over paths
    that follow reduced words with all `m` decorations. In a torsion-free fibre at most
    `m-1` decoration pairs collide.
  * `p_u >= p*`, the Ihara radius at `lam = v + 2m sqrt(2n-1)`.

  This settles the claim in every rank `n >= 3` for uniform multiplicities and
  vertical part empty or `{(1,±1)}`, e.g. `(a;0,1,3),(b;0,1,4),(c;0,1,5),(1,1)` with
  `p_c <= 19/283 < 0.0711 <= p_u`. Mixed multiplicities are covered when
  `p_o(m_lo) < p*(m_hi)`.
  **Where it stops:** rank two. The oriented ensemble uses `3m` of the `4m` decorated
  tree edges, so `p_o m -> 1/3 > 1/(2 sqrt 3) = lim p* m`. For `S_rig`,
  `p_o = 5/44 > 0.0890 = p*`, while simulated `p_c ≈ 0.084`. A rank-two proof must
  count paths that return to a fibre they have already visited, or improve `p*` by
  using short cycles.
* **Excursion second moment, rank two (2026-09-18).**
  `fpbs-tree-projected-rank-two-excursion-second-moment` answers the rank-two
  obstruction above. The trails may, before each step, leave the fibre along any other
  letter and return along the same tree edge with a different decoration, so they use
  all `4m` decorated tree edges. A lumped `2 x 2` transfer matrix (same vertex / same
  fibre) is bounded symbolically by linear height equations and an inequality-forest
  count. Paley–Zygmund then gives `p_c <= 7/(25m)` for every `m >= 40`, whatever the
  heights. With `p* >= 1/(v + 2 sqrt 3 m)`, this settles rank two for:
  * `v = 0`, `m >= 9`;
  * `v = 2`, `m >= 18`;
  * any `v`, `m >= max(40, 10v)`.

  No rigidity is needed. **Where it stops:** small multiplicity. At `m = 3` the
  criterion needs `m p >= 0.373`, while `m p* = 0.267` for `S_rig`. As `m -> infinity`
  the criterion reaches the ensemble's own first-moment limit `0.27258`, and a lower
  limit needs several excursions per slot. `S_rig` is certified separately in
  `fpbs-rigid-f2xz-certified-strict-thresholds`.
  **Obstruction at `m = 3`, `v = 2`** (section 7 of the proof). Take all trails with any
  number of depth-one excursions per slot and no vertical steps. Their first moment
  already vanishes for `p <= p*`: the root of `4m(m-1)p^2 + 3mp = 1` is `0.08967`, while
  `p*(3,2) <= 0.089008`. So no second moment over that class reaches any `m = 3`, `v = 2`
  decoration. A small-`m` route needs vertical steps or deeper excursions, with the
  vertical-step root `0.0777 < p*`, together with an exact pattern transfer. The lumped
  count with vertical steps is worse at every `m` from 3 to 18.
* **Relative gap along a subgroup.** **Where it dies:**
  `fpbs-central-amenable-relative-threshold-is-pu`. The central `Z` makes the
  premise at least as strong as `p_c < p_u` along every infinite subgroup (Attempts
  of the root, 2026-09-12).
* **Critical fibre-sphere bubble.** `fpbs-tree-projected-sphere-bubble-l2-equivalence`
  applies to these graphs, and the route `fpbs-tree-projected-via-critical-sphere-bubble`
  reduces the root to a critical estimate. **Where it stops:** that estimate is open,
  and rigidity gives it no extra structure.
