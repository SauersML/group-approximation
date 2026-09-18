---
rg: 2
id: artin-complex-of-5-3-3-11-is-contractible
kind: claim
title: The Artin complex of the compact hyperbolic Coxeter 4-simplex tree [5,3,3^{1,1}] is contractible
distinct_from:
  artin-complexes-of-5333-and-533-11-are-contractible: that is the conjunction of this case with the path [5,3,3,3]; this is the branched tree alone.
  artin-complexes-of-4335-and-5335-are-contractible: that is the two paths with end labels at least 4; this is the branched tree, which needs a subdivision instead of a path order.
---

Let `Λ = [5,3,3^{1,1}]`: the path `s_1 −5− s_2 −3− s_3`, with two more vertices `s_4, s_5` each
joined to `s_3` by an edge labelled 3. Then the Artin complex `Δ_Λ` is contractible.

By `artin-k-pi-1-from-contractible-artin-complex`, this gives the K(π,1) conjecture for `A_Λ`.

Route `artin-complex-5-3-3-11-contractible-via-b4-subdivision` reduces this claim to
`h4-deligne-complex-upward-flag-toward-5-edge`. That same statement already carries
`[4,3,3,5]` and `[5,3,3,5]`.

## Attempts

- **A path order is unavailable.** `Λ` is not a path, so structure lemma 3 of
  `huang-relative-artin-complex-structure-lemmas` gives no poset on all of `Δ_Λ`.
- **The `(s_4, s_5)`-subdivision works up to H_4** (lane w3-042, 2026-09-17). `Λ` is a copy of
  `B̃_4` with its 4-edge relabelled 5. Huang's subdivision of such complexes (arXiv:2405.12068,
  Proposition `prop:ori link0`) satisfies Haettel's criterion if and only if `H_4` is upward flag
  toward its 5-edge. See the route.
