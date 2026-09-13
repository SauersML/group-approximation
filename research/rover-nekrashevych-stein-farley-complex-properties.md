---
rg: 2
id: rover-nekrashevych-stein-farley-complex-properties
kind: claim
title: The Stein--Farley complex of V_d(G) has labelled-foot stabilizers, simplicial ascending links and G-independent highly connected descending links
distinct_from:
  rover-nekrashevych-finite-presentation-criteria: that imports finite presentation theorems for V_d(G); this states the geometric properties of the Stein--Farley complex that drive every Brown-criterion proof of finiteness and of Sigma^m for V_d(G).
---

**OPEN (input to be verified or proved).** Let `G <= Aut(T_d)` be self-similar, `d >= 2`, and `Γ = V_d(G)`.
Let `C_n` be `n` disjoint copies of `C = X^N`. A *table map* `f: C_n -> C` is a homeomorphism that is a
prefix replacement with a `G`-label on each piece.

**The complex.**

- **Vertices.** Classes `[f]` of table maps modulo precomposition by `Q_n = G^n ⋊ S_n`, which acts on `C_n` by
  labels on the copies and permutations of them. `n` is the height.
- **Order.** `[f] <= [f ∘ E]`, where `E` splits some copies into their `d` subcones.
- **Cells.** `X` is the Stein–Farley cube complex spanned by elementary splittings.
- **Action.** `Γ` acts by postcomposition.

**Claimed properties.**

- (a) `X` is contractible, and for each `n` only finitely many `Γ`-orbits of cells have height `<= n`.
- (b) The stabilizer of a vertex of height `n` is conjugate to `Q_n`. The stabilizer of a cube with bottom vertex
  of height `n` has finite index in that, and it contains every element acting by one label on one copy.
- (c) The ascending link of every vertex of height `n >= 1` is a full `(n-1)`-simplex, so it is contractible.
- (d) The descending link of a height-`n` vertex is the complex of families of pairwise disjoint `d`-subsets of the
  `n` copies, each with a bijection to `X` taken modulo the permutation image `π(G) <= S_d`. It is a complete join
  over the `d`-uniform matching complex on `n` points. For every `m` and `j_0`, its subcomplex of families with at
  most `j` members, `j >= j_0`, is `(m-1)`-connected once `n` is large. The bound is independent of `G`.

## Attempts

- **Sources to read.**
  - K. S. Brown, *Finiteness properties of groups* (1987): Higman–Thompson `V_{d,r}` of type `F_∞`, i.e. trivial `G`.
  - Skipper–Witzel–Zaremsky, *Simple groups separated by finiteness properties*, Invent. Math. 215 (2019).
  - Witzel–Zaremsky and Skipper–Zaremsky on cloning systems.
  - Zaremsky, arXiv:2405.09722, states that self-similar groups of type `F_n` embed in simple groups of type `F_n`,
    which needs `V_(md)(G)` of type `F_n`.
- **Direct route for (d).** Hatcher–Wahl complete join complexes: a complete join over a weakly Cohen–Macaulay
  complex is weakly Cohen–Macaulay of the same dimension. Combine this with the linear connectivity bounds for
  `d`-uniform matching complexes (Björner–Lovász–Vrećica–Živaljević for `d = 2`; Athanasiadis for general `d`).
  Taking at most `j` members is a skeleton, which keeps `(min(m, j-1) - 1)`-connectivity. Constants not checked.
- **Why labels are modded out.** Without `G^n` in `Q_n` the poset is not directed, since two table maps agree after
  refinement only up to labels. So `G` must enter through the stabilizers `Q_n`, and the descending links see only `π(G)`.
- Used by `rover-nekrashevych-higher-sigma-full-via-kernel-brown`.
