---
rg: 2
id: artin-complexes-of-5333-and-533-11-are-contractible
kind: claim
title: The Artin complexes of the compact hyperbolic Coxeter 4-simplex diagrams [5,3,3,3] and [5,3,3^{1,1}] are contractible
distinct_from:
  artin-complexes-of-4335-and-5335-are-contractible: that is the two paths with end labels at least 4, reduced to H_4 flagness; this is the path with an end label 3 and the branched tree, where Haettel's criterion does not apply.
---

For `Λ = [5,3,3,3]` (path `s_1 −5− s_2 −3− s_3 −3− s_4 −3− s_5`) and `Λ = [5,3,3^{1,1}]` (path
`s_1 −5− s_2 −3− s_3` with `s_4, s_5` joined to `s_3` by label 3), the Artin complex `Δ_Λ` is
contractible.

## Attempts

- **Haettel's criterion along the path order fails for `[5,3,3,3]`.** At a vertex of type `ŝ_3`,
  the upper set is the poset of the `A_2` complex on `{s_4, s_5}`. It is a bipartite graph of
  girth exactly 6, and an embedded hexagon gives three pairwise upper-bounded vertices with no
  common upper bound. The reversed order fails the same way at the bottom. The relation `<` is
  a partial order only for the two path orders, since transitivity along `ŝ_i < ŝ_j < ŝ_k` needs
  `s_j` to separate `s_i` from `s_k` in `Λ`.
- **No total order for `[5,3,3^{1,1}]`.** The diagram is not a path, so the poset structure of
  structure lemma 3 is unavailable for `Λ' = Λ`. Possible substitutes: a `(s_4, s_5)`-subdivision in
  the style of Proposition `prop:ori link0` of arXiv:2405.12068, which is used for `B̃_n` cores.
- **Split by diagram; the tree `[5,3,3^{1,1}]` reduced to `H_4`** (lane w3-042, 2026-09-17).
  Route `artin-complexes-5333-and-533-11-by-cases` splits this claim into
  `artin-complex-of-5-3-3-3-is-contractible` and `artin-complex-of-5-3-3-11-is-contractible`.
  For the tree, the `(s_4, s_5)`-subdivision satisfies Haettel's criterion. The lower sets come
  from `d4-subdivided-artin-complex-downward-flag`, and the upper sets need
  `h4-deligne-complex-upward-flag-toward-5-edge`. Hypothesis 3 holds **iff** that `H_4` statement
  does. See route `artin-complex-5-3-3-11-contractible-via-b4-subdivision`.
  So `[4,3,3,5]`, `[5,3,3,5]` and `[5,3,3^{1,1}]` all hang on that single statement, and
  `[5,3,3,3]` stays without a reduction.
- **Huang's proposed strategy** (arXiv:2405.12068, Conjecture `conj:exceptional`, which names
  `[5,3,3,3]` as exceptional): give each simplex the shape of the compact hyperbolic simplex
  and prove CAT(1) vertex links. The links are spherical Deligne complexes of `H_4`, `A_4` and
  their products with smaller types. Not attempted.
- **Connectivity.** `Δ_Λ` is simply connected (structure lemma 1). The first open homotopy
  invariant is `H_2(Δ_Λ)` (compare `deligne-connectivity-iff-artin-complex-connectivity`).
