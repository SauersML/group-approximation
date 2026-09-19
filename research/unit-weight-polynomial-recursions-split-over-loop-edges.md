---
rg: 2
id: unit-weight-polynomial-recursions-split-over-loop-edges
kind: claim
title: A fully self-replicating group with perfect transitive root group fixes a vertex of every tree whose edge stabilizers contain no coordinate copy of G'; so the amalgam obstruction holds over infinite edge groups, and every unit-weight polynomial M_11 recursion whose loop-graph star has small edges and proper factors is not finitely presented, for any number of letters and for section cycles
artifacts:
  - experiments/poly-star-obstruction-2026-09-19/poly_star_screen.py
  - experiments/poly-star-obstruction-2026-09-19/poly_star_screen.out
distinct_from:
  linear-m11-bouquet-recursions-are-not-finitely-presented: that needs the shared sub-basis to have finite image and uses one-endedness; this replaces one-endedness by a fixed-point lemma for commuting coordinate subgroups, so edge groups may be infinite (any cyclic group, or any subgroup of lower activity degree), and it applies to any number of state letters and to section cycles, not only two-letter bouquets.
  same-point-loop-recursions-reduce-to-loop-graph-words: that locates the stable relators in the loop-graph factors C_c under (U) and (L1) at level 1; this uses that location (at level p) to build a tree of free factors (centre = lower letters, leaves = loop-graph components) and decides finite presentability from it.
  pure-loop-self-replicating-groups-are-not-fp: that is the free-product case (empty edges); this is the tree-of-free-factors case with nonempty edges.
---

**ESTABLISHED (unreviewed).** Proof: `unit-weight-polynomial-recursions-split-over-loop-edges-proof`.
Items 1–4 are proved by hand. Item 5 is a finite exact screen (`poly_star_screen.py`).
Points are coded `0..10`, `α` is the 11-cycle and `β = (0 1 2 3 7)(4 9 6 10 5)`, as in the
cited scripts.

**Setting.** As in `pure-loop-self-replicating-groups-are-not-fp`: `G = F/K` is fully
self-replicating (`G = G^X ⋊ P`, `P ≤ G`), with (SF), `ρ : F ↠ G`, and `Q^∞` the stable part
of the section closure of a finite normal generating set of `K`. `ι_y : G → G` puts an
element at the vertex `y ∈ X`. `G'` is the commutator subgroup.

**Theorem.**

1. **(Lemma T, coordinate fixed points.)** Let `G` be finitely generated and fully
   self-replicating, with `|X| ≥ 2` and `P` perfect and transitive (e.g. `M_11`). Let `G`
   act on a tree without inversions. Then either `G` fixes a vertex, or some edge stabilizer
   contains `ι_y(G')` for some `y ∈ X`. Also `G' = ⟨⟨P⟩⟩_G`, and the `G`-conjugates of
   `ι_y(G')` are the `ι_z(G')`.

2. **(Tree-of-factors obstruction.)** Let `F` have a basis `B`, and let `B_v` (for the
   vertices `v` of a finite tree `Y`) be sub-bases with `⋃ B_v = B`, such that the vertices
   whose sub-basis contains a given letter span a subtree. Put `E_e = B_v ∩ B_w` for each
   edge `e = vw`. Suppose that
   - (i) whenever `G` is finitely presented, every word of `Q^∞` is conjugate into some
     `F(B_v)`;
   - (ii) no `ρ(F(E_e))` contains any `ι_y(G')`;
   - (iii) no `ρ(F(B_v))` equals `G`.

   Then `G` is **not finitely presented**. No finiteness of the edge images is needed. If
   `P` is not perfect, (ii) can be replaced by: no `ρ(F(E_e))` contains an infinite locally
   finite subgroup.

3. **(Polynomial loop star.)** Assume (U): every letter section has at most one state
   letter. Assume also (Poly): every strongly connected component of the signed
   weight-preserving digraph is a single directed cycle (self-loops and section cycles
   such as `s → t → s` or `s → t → s^{-1} → t^{-1} → s` are allowed).
   - Let `p` be the lcm of the cycle lengths, and assume (L1_p): every cycle letter has
     exactly one level-`p` self-loop `s|_{x_s} = A_s s B_s` (`|x_s| = p`). Call
     `ℓ_s = A_s s B_s` its loop.
   - Degrees: rooted letters get `−1`. A cycle letter gets `1 +` the maximum degree of the
     letters it reaches outside its cycle. Any other letter gets the maximum degree of the
     letters it reaches. Let `d` be the top degree.
   - `D` is the set of letters reachable from a cycle letter through a section that leaves
     its cycle. `Λ` runs over the components of the level-`p` loop graph (vertices `X^p`,
     one edge per loop). Put `E_Λ = Λ ∩ D`.
   - (N) holds if every loop is nontrivial in `G`.

   Assume (N) and `d ≥ 1`. Suppose that every component `Λ` satisfies either (free) or
   both (a) and (b):
   - (free) the loops of `Λ` lying in `D` form a forest in `Λ`, and `rank π_1(Λ) ≤ 1`;
   - (a) `|E_Λ| ≤ 1`; or every letter of `E_Λ` has degree `< d` and `G'` contains an
     element with a section `c s'^{±1} c'` (with `c, c'` rooted and `s'` a top-degree cycle
     letter);
   - (b) `Λ` contains no top-degree letter, or `⟨ρ(ℓ_s) : s ∈ Λ⟩` is proper in `G` (for
     instance, its root image is proper in `P`, or it is intransitive on some level).

   Then `G` is **not finitely presented**. The splitting is a star.
   - Its centre is `F(R ∪ D)`, where `R` is the set of rooted letters.
   - Each (a)(b) component gives a leaf `F(ℓ_s : s ∈ Λ)`, attached by the edge
     `F(ℓ_s : s ∈ E_Λ)`.
   - Each (free) component gives the leaf `C_c = λ(π_1(Λ, c))`, which is trivial or cyclic,
     attached by an empty edge.
   - Every remaining letter gets its own free leaf.
   - The centre maps into the polynomial-activity group `Pol(d − 1)`, while top-degree
     letters have activity of order `n^d`. So its image is proper automatically, and (a)
     never needs the edge loops to have finite order.
   - For `d = 0`, `G` is a bounded automaton group, which is contracting and not finitely
     presented.

4. **(Commuting-coordinate consequence.)** For `M_11` recursions under (U) and (Poly), the
   only way to escape item 3 is (N) failing, or some component failing (free) together
   with one of the following:
   - (α) two or more loops of the component lie in `D` and at least one has top degree; or
   - (β) `G'` has no top-degree section of the stated form; or
   - (γ) some loop-graph component failing (free) contains a top-degree letter, and its
     loops generate `G`. Failing (free) means rank `≥ 2`, or a cycle of `D`-loops, such as
     a bouquet containing a lower loop. Or:
   - leaving (U) or (Poly) altogether (weight `≥ 2`, or exponential activity).

   Nontrivial loops are never finitary, so "a finite-order loop with a section-closed
   letter block" (the design rule of the bouquet node) is no longer the obstruction. The
   obstruction is now (γ): which loops generate `G`.

5. **(Screen.)** See the data section below.

## Data (item 5)

`poly_star_screen.py` checks four three-letter M_11 families exactly. Each is fully
self-replicating, with root permutations drawn from 8 words and decorations from `{"", a}`.
That is 4096 recursions per family, 16,384 in all:
- *chain*: `s → t → u`;
- *fan*: `s → t ← u`;
- *cycle*: the section cycle `s → t → s`, with exit `s → u`;
- *scycle*: the signed cycle `s → t → s^{-1} → t^{-1} → s`, with exit `s → u`.

Every member satisfies (U), (Poly), (L1_p) and (N), with `d ≥ 1`. None is bounded, none is
exponential, and none has a trivial loop.

| family | `p` | killed by item 3 | survivors |
|---|---|---|---|
| chain  | 1 | 3304 | 792 |
| fan    | 1 | 3738 | 358 |
| cycle  | 2 | 3894 | 202 |
| scycle | 4 | 4075 | 21 |
| total  |   | 15011 | 1373 |

Most kills are pure (free) splittings; see the `.out` for the breakdown.
- Fan and cycle members with only (free) components: 3634 and 3678.
- Chain kills using (a2), where the edges are infinite and exceed rank 1: 268.
- Stars that have an edge loop with no finite order `≤ 60`: 367.

These last two groups are exactly what the bouquet node's finite-edge amalgam cannot handle.

**Survivors.** Every survivor satisfies (a) and fails (b) in exactly one component, which also fails (free)
and contains all three letters `s, t, u`. In the printed survivors this component has three
loops on at most two vertices, so its rank is at least 2. In every one of the 48 survivors whose level-2 image
was computed (12 per family), the loops generate a group that is root-transitive,
transitive on levels 2 and 3, and has full level-2 image `M_11 ≀ M_11` (order `7920^{12}`).
So these are (γ)-candidates: the level-1, level-2 and level-3 tests do not separate
`⟨loops⟩` from `G`.
Whether `⟨ρ(ℓ_s), ρ(ℓ_t), ρ(ℓ_u)⟩ = G` is open for them. If it is proper, item 3 kills the
recursion. If it equals `G`, the star has a leaf mapping onto `G`, and the obstruction
genuinely fails. For example, the first chain survivor has root words
`(ps, pt, pu) = (a, a, e)` and no decorations.
