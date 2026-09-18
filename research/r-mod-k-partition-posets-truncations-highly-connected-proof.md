---
rg: 2
id: r-mod-k-partition-posets-truncations-highly-connected-proof
kind: route
title: Import Wachs's nonpure shellability of the k mod d partition posets, bound facet dimensions by atom block counts, then delete the coarse partitions one at a time along joins
target: r-mod-k-partition-posets-truncations-highly-connected
requires: []
---

This is a citation import plus an elementary derivation. Notation is that of the claim.

## Sources

Both were read in full text on 2026-09-18, with the text extracted by `pypdf`. Quotations are verbatim up to
typesetting (`Π` for the partition symbol, `0̂`/`1̂` for bottom and top, `∈`, `⊆`).

**(W99)** M. L. Wachs, *Whitney homology of semipure shellable posets*, J. Algebraic Combin. 9 (1999), 173–207,
Section 3.

- Setup: "Given any set T ⊆ P, where 1 ∉ T, let Π^T_n be the induced subposet of Π_n consisting of 0̂, 1̂ and all
  partitions of [n] whose block sizes are in T. If 1 ∈ T, then in order for our results to hold we let Π^T_n be the
  induced subposet as above with a new minimum element 0̂ attached below 1/2/.../n."
- Definition 3.1: "Let d ∈ P. We shall say that T ⊆ P is d-additive if for all t_1, t_2, ..., t_j ∈ T, we have
  t_1 + t_2 + ··· + t_j ∈ T if and only if j ≡ 1 mod d."
- Definition 3.2: "We shall say that a nonempty subset T ⊆ P is subtractive if for all t_1, t_2 ∈ T,
  t_1 + t_2 − min T ∈ T."
- Example 3.8: "For fixed integers k ≥ 1 and d ≥ 1, let T = {k + id | i = 0, 1, 2, ...} and let d_0 = d/gcd(d,k).
  Then T is d_0-additive and subtractive."
- Theorem 3.14: "Let T ⊆ P be d-additive and subtractive. Then the lexicographical order of the atoms of Π^T_n is a
  recursive atom ordering. Consequently Π^T_n is shellable."
  - The proof begins: "We prove the result for n ∈ T. When n ∉ T, the proof below requires slight modification which
    we leave to the reader." We use only `n ∈ T`, the case written out in full.
- Section 1, p. 179: "We say that a bounded poset P has the vanishing homology property (resp., is shellable,
  sequentially Cohen-Macaulay) if its order complex Δ(P̄) [...] is shellable". The proper part `P̄` is `P` minus
  `0̂` and `1̂`.

Wachs's `(k, d, d_0)` are our `(r_0, k, k')`. Her `T` is our `T`, and `n ∈ T` is our standing assumption.

**(WN)** M. L. Wachs, *Poset Topology: Tools and Applications*, arXiv:math/0602226v2 (the notes already imported in
`one-mod-k-partition-posets-are-highly-connected-proof`).

- Theorem 3.1.3 (Björner and Wachs, *Shellable nonpure complexes and posets I*, Trans. AMS 348 (1996)): "A shellable
  simplicial complex has the homotopy type of a wedge of spheres (in varying dimensions), where for each i, the number
  of i-spheres is the number of i-facets whose entire boundary is contained in the union of the earlier facets."
- Section 5.1: "A result of Quillen [135] states that if P and Q have bottom elements 0̂_P and 0̂_Q, respectively, then
  there is a (G × H)-homeomorphism P × Q \ {(0̂_P, 0̂_Q)} ≅ P \ {0̂_P} ∗ Q \ {0̂_Q}." Here [135] is Quillen,
  *Homotopy properties of the poset of nontrivial p-subgroups of a group*, Adv. Math. 28 (1978). The statement is about
  order complexes. Reversing all orders does not change an order complex, so it holds equally for posets with top
  elements and the product minus its top.

**Certificate boundary.** W99 Theorem 3.14, the Björner–Wachs theorem and Quillen's homeomorphism are used as
published theorems. Everything else is proved below.

## Derivation

Write `b(x)` for the number of blocks of `x`. All posets are ordered by refinement, with coarser partitions larger.

**(a) Merges.** Let `t_1, ..., t_j in T`. Then `Σ t_i ≡ j r_0 mod k`, and `j r_0 ≡ r_0 mod k` iff `k | (j − 1) r_0`
iff `k' | (j − 1)`, since `gcd(r_0/g, k') = 1`. So a union of `j` blocks of sizes in `T` has size in `T` iff
`j ≡ 1 mod k'` (the size is `>= r_0` automatically). This is W99's `k'`-additivity, proved directly.

**Item 1.** If `y >= x`, each block of `y` is a union of blocks of `x` with size in `T`, so by (a) it is a union of
`j ≡ 1 mod k'` blocks.

- Suppose some block of `y` absorbs `j >= 2k' + 1` blocks of `x`, or two blocks of `y` each absorb more than one. Merge
  just `k' + 1` of the `x`-blocks inside one `y`-block. By (a) this gives `z in Π^T(S)` with `x < z < y`.
- So covers merge exactly `k' + 1` blocks, and each cover lowers `b` by `k'`.
- If `|S| in T`, the one-block partition is in `Π^T(S)` and lies above every `x`. So `b(x) ≡ 1 mod k'`, and every
  maximal chain from `x` up to it has `(b(x) − 1)/k'` covers.

**Item 2.** Let `t in T` with `t >= (k' + 1) r_0`. Put `t_0 = t − k' r_0`. Then `t_0 >= r_0` and
`t_0 ≡ t mod k`, because `k' r_0 = k (r_0/g)`. So `t_0 in T`, and `t = t_0 + r_0 + ... + r_0` with `k' + 1` summands.
Splitting such a block gives a strictly finer member of `Π^T(S)`. Hence in a minimal element every block has fewer than
`(k' + 1) r_0` points, and there are more than `|S| / ((k' + 1) r_0)` blocks.

**Item 3.** Let `s in T`.

- By W99 Theorem 3.14 with Example 3.8, `Π^T_s` is shellable. So `Δ` of its proper part `Π^T([s]) \ {1̂}` is a
  shellable simplicial complex. (For `r_0 = 1` the adjoined `0̂` is not a partition. For `r_0 >= 2` the bottom
  `1/2/.../s` is not in `Π^T([s])`. Either way the proper part is `Π^T([s])` minus the one-block partition.)
- A facet of that complex is a maximal chain `a = x_1 < ... < x_p` of the proper part: `a` is minimal, `x_p` is a
  coatom and each step is a cover. By item 1, `p = (b(a) − 1)/k'`. By item 2, `b(a) > s/((k' + 1) r_0)`.
- So every facet has dimension `p − 1 > s/c − 1/k' − 1 >= s/c − 2`, with `c = (k' + 1) r_0 k'`. Since the dimension is
  an integer, it is at least `⌊s/c⌋ − 1`.
- By the Björner–Wachs theorem the complex is a wedge of spheres, each of dimension at least `⌊s/c⌋ − 1` (a point if
  the wedge is empty). So it is `(⌊s/c⌋ − 2)`-connected, and in particular `κ(s)`-connected.

**(b) Refinement posets are joins.** Let `x in Π^T([n])` have blocks `B_1, ..., B_p`. The partitions strictly finer
than `x` form `W_x = (Π^T(B_1) × ... × Π^T(B_p)) \ {top}`, where the top is `x` itself. Each `Π^T(B_i)` has the top
`{B_i}`. Quillen's homeomorphism (top version), applied `p − 1` times, gives

    Δ(W_x) ≅ Δ(Π^T(B_1) \ {B_1}) ∗ ... ∗ Δ(Π^T(B_p) \ {B_p}).

- A factor with `Π^T(B_i) = {B_i}` contributes the empty complex, the unit of the join.
- A join `A ∗ A'` is at least as connected as `A` (connectivity adds, plus 2, and the empty set is `(−2)`-connected).
- So `Δ(W_x)` is at least as connected as `Δ(Π^T(B_i) \ {B_i})` for each `i`. Since `|B_i| in T`, item 3 applies.

**Item 4.** Start from `K_0 = Δ(Π^T([n]) \ {1̂})`, which is `κ(n)`-connected by item 3. The elements of
`Π^T([n]) \ {1̂}` outside `Z(n, L)` are the finitely many `x` with `2 <= b(x) <= L − 1`. Delete them one at a time in
order of nondecreasing `b(x)`.

- When `x` is deleted, every element coarser than `x` has fewer blocks and is already gone. Elements with as many blocks
  as `x` are incomparable to `x`. Every element finer than `x` is still present, since it has more blocks. So the link
  of the vertex `x` in the current complex is `Δ(W_x)`.
- `x` has at most `L − 1` blocks, so one block `B` has `|B| >= n/(L − 1)`, that is `|B| >= ⌈n/(L − 1)⌉`. By (b) and
  item 3, the link is `κ(|B|)`-connected, and `κ(|B|) >= κ(⌈n/(L − 1)⌉) =: κ_L`, since `κ` is nondecreasing.
- Deleting a vertex `v` whose link is `c`-connected: `K = (K \ v) ∪ (v ∗ lk v)`, glued along `lk v`. Coning off a
  `c`-connected subcomplex gives a `(c + 1)`-connected pair, so `π_i(K \ v) -> π_i(K)` is an isomorphism for `i <= c`.
- So every deletion preserves `π_i` for `i <= κ_L`.

After all deletions the complex is `Δ(Z(n, L))`. Since `κ_L <= κ(n)`, `π_i(Δ(Z(n, L))) ≅ π_i(K_0) = 0` for
`i <= κ_L`. ∎

**Sanity checks.**

- `k = 1` (`T` is all positive integers): `Π^T` is the partition lattice. Item 3 gives `(⌊s/2⌋ − 2)`-connected, which
  is weaker than the sharp `(s − 4)` of Björner, `Π̄_s ≃ ∨ S^{s−3}`.
- `k = 2`, `r_0 = 2` (even blocks): item 1 says covers merge 2 blocks, and item 2 says minimal elements are perfect
  matchings. This matches Wachs's `d`-divisible lattice `Π^{0 mod 2}_{2m}`, whose proper part is a wedge of
  `(m − 2)`-spheres (WN Exercise 4.3.6 (d)).
- A block count that goes up by more than `k'` along a cover cannot occur. So the upper intervals are the pure
  `Π^{1 mod k'}` lattices, as in W99 Lemma 3.11.
