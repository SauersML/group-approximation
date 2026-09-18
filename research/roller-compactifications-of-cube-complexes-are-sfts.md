---
rg: 2
id: roller-compactifications-of-cube-complexes-are-sfts
kind: claim
title: For a free cocompact action on a CAT(0) cube complex, the radius-2 distance-gradient SFT is exactly the Roller compactification (HL holds, seeds are principal); vertex-transitive actions (RAAGs) give (IE′), every virtually special group virtually embeds in a RAAG, and no overgroup of an infinite Kazhdan group has such an action
requires:
  - horofunction-lemma-holds-for-free-and-surface-groups
  - finite-type-branch-blow-ups-are-sft-compactifications
---

**ESTABLISHED** (lane proof, bh-invent-13, 2026-09-18; elementary; not reviewed): parts 1–3. Parts 4–5 combine them with
cited theorems. No priority is claimed for the coding of the Roller compactification by hyperplane orientations, which
is standard. The new point is that it is of finite type, with isolated seeds.

**Setting.**
- `S` acts freely and cocompactly on a (finite-dimensional, locally finite) CAT(0) cube complex `X`, with vertex orbits
  `S·x_0, …, S·x_{m−1}`.
- `d` is the combinatorial metric on `X^0`: the number of hyperplanes separating two vertices.
- Functions `f : X^0 → Z` modulo constants are coded by their gradients on edges. Writing `X^0 = S × {0,…,m−1}`,
  these are S-configurations over a finite alphabet, and the cocycle condition on squares is local.
- `Y_2` is the SFT of gradient fields whose restriction to every ball `B_2(v)` of `X^1` is, up to a constant, that of
  some `d(·,q)`, `q ∈ X^0`.
- `\bar X` is the Roller compactification, i.e. the set of all ultrafilters. An ultrafilter chooses one halfspace
  `o(H)` of every hyperplane `H`, with the chosen halfspaces pairwise intersecting.

## Statement

1. **(HL) for median metrics.** `Y_2` is S-conjugate to `\bar X`: `f ↦ o_f`, where `o_f(H)` is the descending side.
   In particular every point of `Y_2` is a limit of distance functions `d(·,q)`, `q ∈ X^0`.
2. **Seeds.** `f ∈ Y_2` has a local minimum at `x` iff `f = d(·,x) + c`. So the principal ultrafilters are exactly the
   isolated points of the form "local minimum at `x`". Each orbit `S·∇d(·,x_i)` is open and discrete, with trivial
   stabilizers.
3. **(IE′) when `m = 1`.** If `S` acts freely and transitively on `X^0`, then `(Y_2, ∇d(·,x_0)|_{B_2})` is an SFT
   compactification of `S` in the sense of `finite-type-branch-blow-ups-are-sft-compactifications`. This covers every
   RAAG `A_Γ` with its standard generators, and `Z^n` and `F_n` in particular.
4. **Caveat for `m > 1`.** Take `S = Z` acting on the ladder `Z × [0,1]`. The closure of one vertex orbit misses two of
   the four Roller boundary points. So `\bar X` compactifies the S-set `S × m`, and a single orbit need not be dense.
5. **Virtually special groups.** A virtually special group has a finite-index subgroup `S'` that embeds in a RAAG
   (Haglund–Wise, local isometry to a Salvetti complex), and that RAAG has (IE′) by 3. By Agol, every hyperbolic group
   acting properly and cocompactly on a CAT(0) cube complex is virtually special. So every cubulated hyperbolic group,
   and so most 3-manifold groups (Agol, Wise, Przytycki–Wise), is virtually contained in a group with an SFT
   compactification.
6. **Kazhdan groups are out of reach of cubes, even via overgroups.**
   - A group with (T) fixes a point in every action on a CAT(0) cube complex (Niblo–Reeves 1997, finite-dimensional case; Niblo–Roller 1998). A fixed point in a cube gives a finite-index subgroup fixing a vertex.
   - Any overgroup `Λ ⊇ H` acting properly on a cube complex restricts to a proper action of `H`.
   - So no group containing an infinite Kazhdan group acts properly on a CAT(0) cube complex.

## Proof

**Orientations.**
- `X^1` is bipartite, so every `∇d(·,q)` takes values `±1`.
- In a square, opposite edges are dual to one hyperplane and are oriented alike in any distance pattern. Every square
  lies in `B_2` of its corners, so `f ∈ Y_2` defines `o_f(H)` for every hyperplane (edges dual to `H` are connected
  through squares).
- `f(y) − f(x)` counts the separating `H` with `x ∈ o_f(H)`, minus those with `y ∈ o_f(H)`. So `f` is determined by
  `o_f`, and `∇d(·,q)` corresponds to the principal ultrafilter at `q`.

**The 1-ball rule.** The descending edges of `d(·,q)` at `x` are those whose hyperplanes separate `x` from `q`.

Let `x` have two edges `xa`, `xb` dual to disjoint hyperplanes `H_1`, `H_2`, and let `h_i` be the side not containing `x`.
- Of the four intersections `h_1^{(*)} ∩ h_2^{(*)}` exactly one is empty.
- `x ∈ h_1^* ∩ h_2^*`, `a ∈ h_1 ∩ h_2^*` and `b ∈ h_1^* ∩ h_2`, since an edge crosses only one hyperplane.
- So `h_1 ∩ h_2 = ∅`, and no `q` makes both edges descending.

Hence `f ∈ Y_2` has no vertex with two descending edges dual to disjoint hyperplanes.

**`o_f` is an ultrafilter.**
- *Crossing pairs.* All four quadrants of two crossing hyperplanes contain vertices, so any two choices intersect.
- *Disjoint pairs.* Suppose `o_f(H_1) ∩ o_f(H_2) = ∅`. Choose such a pair with the fewest hyperplanes `N` separating
  `H_1` from `H_2`.
  - *Descent.* A separating `V` would give, according to `o_f(V)`, a pointing-away pair `(H_1,V)` or `(V,H_2)` with
    smaller `N`. So `N = 0`.
  - *Adjacency.* The hyperplanes separating the convex sets `o_f(H_1)` and `o_f(H_2)` are then only `H_1` and `H_2`.
    So `d(o_f(H_1), o_f(H_2)) = 2`, via a geodesic `a–x–b` that crosses `H_1` and then `H_2`, the other order being
    impossible. So `x` has two descending edges dual to the disjoint hyperplanes `H_1`, `H_2`.
  - This contradicts the 1-ball rule.

**Part 1.**
- (⇒) `o_f` is an ultrafilter. By Helly for convex subcomplexes (Helly number 2, Roller/Sageev), every finite family
  `F` of chosen halfspaces has a common vertex `x_F`. Taking `F` to be the hyperplanes dual to the edges of `B_n(v)`,
  we get `f = d(·,x_F) + c` on `B_n(v)`, since paths inside the ball cross only hyperplanes of `F`. So `f` is a limit
  of distance functions.
- (⇐) An ultrafilter defines an `f` in the same way, and `f ∈ Y_2` because each `B_2` pattern is realized by `x_F`.
- The map is S-equivariant and a homeomorphism (product topologies on both sides), so `Y_2 ≅ \bar X`.

**Part 2.** Suppose `x` is a local minimum of `f` but `x ∉ o_f(H)` for some `H`.
- Let `p` be the gate projection of `x` onto the convex set `o_f(H)`. The hyperplane `K` of the first edge of `[x,p]`
  separates `x` from all of `o_f(H)`, so its side `k ∌ x` contains `o_f(H)`.
- Ultrafilters are upward closed (if `o_f(K) = k^*`, then `k^* ∩ o_f(H) = ∅`, contradicting pairwise intersection),
  so `o_f(K) = k`.
- Then the edge at `x` dual to `K` descends, and `x` is not a local minimum. Contradiction.
- So `o_f` is principal at `x`. Stabilizers are trivial because the action on `X^0` is free, and each principal point
  is isolated by its `B_2` pattern.

**Part 3.** With `m = 1`, `X^0 = S·x_0`, so the principal points form one orbit, dense in `\bar X` by part 1. So (C1)
and (C2) hold.
- For `A_Γ`, the universal cover of the Salvetti complex is a CAT(0) cube complex whose 1-skeleton is the Cayley
  graph for the standard generators.
- `Z^n`: the cube lattice. `F_n`: the tree.
- Calibration: `Z²` gives the product `C_Z ⊠ C_Z` of the gluing node, and `F_n` recovers
  `horofunction-lemma-holds-for-free-and-surface-groups` part 1.

**Part 4.** The ladder's hyperplanes are the horizontal midline `M`, dual to the rungs, and the vertical hyperplanes `V_n`, dual to the horizontal edges. The Roller boundary is
`{±∞} × {top, bottom}`. Principal ultrafilters at bottom vertices choose the bottom side of `M`, and so does every
limit of them.

## What remains for Kazhdan hyperbolic groups

- The median proof uses three things: a halfspace calculus computing the metric, Helly number 2, and a one-step
  descent to adjacent hyperplanes.
- By part 6, a Kazhdan hyperbolic group (a uniform `Sp(n,1)` lattice, a Żuk group) has no such calculus, in itself or
  in any cubulated overgroup. It is also not a surface group, so the wall argument of the surface node does not apply.
- What is left for them is exactly general (HL) for the distance-gradient SFT `Y_R` of a hyperbolic Cayley graph. This
  is the tube lemma that bh-g2-buildings holds, along Coornaert–Papadopoulos Prop. 3.4. Seed uniqueness (parent,
  4a) is already proved.
- The simple Kazhdan inputs `H_Γ` are neither hyperbolic nor cubulable, so they need a Helly-type halfspace system
  that is neither median nor hyperbolic.

## Lesson for general BH

- For median geometries the horofunction lemma costs nothing. Local realizability on 2-balls forces an ultrafilter:
  the descent to adjacent hyperplanes is one step, and Helly number 2 does the rest. So Roller compactifications are
  SFT compactifications with isolated principal seeds. Every RAAG, and virtually every special group, has one.
- But cubes can never carry Kazhdan inputs, not even through overgroups, because proper cube actions restrict to
  subgroups and (T) forbids them. For Kazhdan inputs the seed must come from a non-median Helly system: horospheres
  in the hyperbolic case (the tube lemma), and an unknown system for the simple `H_Γ`. That is the sharp form of the
  remaining (IE′) gate.

## Referee (bh-ref-hl, 2026-09-18): PASS

This is an internal lane review.
- **The 1-ball rule.** For disjoint hyperplanes exactly one quadrant is empty, and here it is `h_1 ∩ h_2`, so no target makes both
  edges descending. Correct.
- **`o_f` is well defined.** Squares lie in `B_2`, opposite square edges are oriented alike, and hyperplane carriers are connected.
  Correct.
- **Ultrafilter.**
  - Crossing pairs always intersect.
  - For a minimal pointing-away pair, a separating `V` yields a closer pair whichever side `o(V)` takes. So `N = 0`.
  - A hyperplane separating `o(H_1)` from `o(H_2)` cannot cross either of them, since crossing puts both of its sides into the
    halfspace. So only `H_1, H_2` separate them, giving the path `a–x–b` with two descending edges dual to disjoint
    hyperplanes, which contradicts the 1-ball rule. Correct.
- **Part 1.** Helly number 2 for halfspaces (Roller, Sageev) gives `x_F`. Paths inside a ball cross only hyperplanes in `F`. The
  equivariant homeomorphism is in product topologies. Correct.
- **Part 2.** Gate projection onto `o_f(H)` plus upward closure gives a descending edge at a non-principal local minimum. Correct.
- **Parts 3–6.** The ladder caveat is correct. The cited inputs are standard and were recalled, not re-read: Haglund–Wise (virtual
  embedding in RAAGs), Agol (cubulated hyperbolic groups are virtually special), and Niblo–Reeves / Niblo–Roller ((T) ⇒ fixed
  point).
- **Scope note.** Part 5 correctly says "virtually contained in a group with an SFT compactification", not that every virtually
  special group itself has one.
