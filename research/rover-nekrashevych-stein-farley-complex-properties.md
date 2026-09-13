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
- (b) The stabilizer of a vertex of height `n` is conjugate to `Q_n`. The stabilizer of a cell with bottom vertex of
  height `n` has finite index in that and contains all of `G^n`: a label on one copy maps each splitting of that copy
  to a splitting of the same vertex class, by self-similarity.
- (c) For every `n_1`, the superlevel subcomplex on heights `>= n_1` is contractible. Its poset is directed, since an
  upper bound of two tall vertices is tall.
- (d) The descending link of a height-`n` vertex inside the superlevel subcomplex `>= n_1` is `(m-1)`-connected once
  `n` is large, for every fixed `m` and `n_1`. The bound is independent of `G`: the labels are modded out, and only
  the permutation image `π(G) <= S_d` affects merges.

## Attempts

- **Sources read 2026-09-13 (MSI, extracted PDF text; lane z1-14-rover-nek).**
  - R. Skipper and M. C. B. Zaremsky, *Almost-automorphisms of trees, cloning systems and finiteness properties*,
    arXiv:1709.06524v2.
    - Corollary 2.7: `V_d(G) ≅ T(S_* ≀ G)`, the Thompson-like group of a d-ary cloning system on `S_n ≀ G`.
    - Section 3: a poset complex `|P^1_H|` on which `V_d(G)` acts (fixed subgroup `H <= G`).
    - Lemma 3.7: the vertex stabilizer is `S_n ≀ H`, and simplex stabilizers relate to it.
    - Corollary 3.8: simplex stabilizers have finite index in some `S_n ≀ H`, so they are `F_∞` when `H` is.
    - Lemma 3.9: cocompactness. Lemma 3.11: contractibility when `H` is nuclear. Proposition 4.12: retraction to the
      `H`-Stein–Farley complex. Section 4.3: descending links.
    - **Corollary 4.28** (verbatim up to typesetting): "Let G ≤ Aut(T_d) be self-similar and of type F_∞. Then
      V_d(G) is of type F_∞."
    - **Remark 2.8** says a d-ary analog of Witzel–Zaremsky Proposition 5.9 "would quickly prove" this, but it is not
      developed there. So no finite-`m` statement (`G` of type `F_m` ⇒ `V_d(G)` of type `F_m`) is in that paper.
  - S. Witzel and M. C. B. Zaremsky, *Thompson groups for systems of groups, and their finiteness properties*,
    arXiv:1405.5491 (binary cloning systems).
    - Lemma 4.9 (properly graded): the vertex stabilizer is `G_n`, and cell stabilizers have finite index in `G_n`.
    - Theorem 5.3: Brown's criterion. Section 5.3: descending links `L_n(G_*)`.
    - **Proposition 5.9**: properly graded, `G_n` eventually of type `F_n`, and `L_n(G_*)` eventually `(n−1)`-connected
      imply `T(G_*)` is of type `F_n`.
- **Status of (a)–(d).**
  - For `G` of type `F_∞`, taking `H = G` in Skipper–Zaremsky gives (a), (b) up to the containment of `G^n`
    (checked by hand as above) and the descending-link connectivity used for Corollary 4.28.
  - (c) is elementary.
  - (d) for the superlevel truncation is not stated in either source. Truncating removes merges that go below height
    `n_1`, so the needed complex is a bounded-size part of their descending link; its connectivity still has to be
    written down.
  - For finite `m`, the d-ary analog of Witzel–Zaremsky Proposition 5.9 is the missing written step.
- **Direct route for (d).** Hatcher–Wahl complete join complexes over `d`-uniform matching complexes
  (Björner–Lovász–Vrećica–Živaljević for `d = 2`, Athanasiadis for general `d`). Constants not checked.
- **Why labels are modded out.** Without `G^n` in `Q_n` the poset is not directed, since two table maps agree after
  refinement only up to labels.
- Used by `rover-nekrashevych-higher-sigma-full-via-kernel-brown`.
