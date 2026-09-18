---
rg: 2
id: free-products-with-z-inherit-m2-from-universal-points
kind: claim
title: If A has a computable hyperaperiodic point that is universal at the origin, then A * Z carries an effectively closed minimal free subshift; minimality is supplied by the Bass-Serre tree
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2) for a given group; this proves (M2) for A * Z assuming only a POINTWISE property (U)+(H) of A, with no minimality and no global recurrence anywhere in A.
  effectively-rf-groups-have-effective-minimal-free-subshifts: that uses a profinite skeleton and needs residual finiteness; this uses a Bass-Serre tree skeleton and applies to non-residually-finite A.
  gjs-countable-groups-have-free-minimal-subflows: that is non-effective and gives minimality directly on A; this gets minimality from the free product, with effectivity.
---

**ESTABLISHED (lane proof, bh-g1-effective, 2026-09-18; not independently reviewed).**

**Conventions.**
- `A` is finitely generated, with finite generating set `S_A` and solvable word problem.
- `B = ⟨b⟩ ≅ Z`, `Γ = A * B`, and `S = S_A ∪ {b}`. Word length is `|·|`; for `a ∈ A`,
  `|a| = |a|_{S_A}`.
- Configurations are maps `Γ → C` with `(λ·z)(μ) = z(μλ)`. The pattern of `z` at `μ` of
  radius `r` is `σ ↦ z(σμ)` on `B(r)`.
- For `A`, a pattern of `y ∈ C_A^A` at `g` is `a ↦ y(ag)` on `B_A(r)`, and
  `(a_0·y)(a) = y(aa_0)`.

**Hypotheses on A.** There is a computable `y_A ∈ C_A^A` (finite alphabet) with:
- **(H) hyperaperiodic:** for each `s ∈ A∖{1}` there is `R(s)` such that for every `g ∈ A`
  some `a ∈ B_A(R(s))` has `y_A(ag) ≠ y_A(asg)`. Equivalently, the orbit closure `O_A` is a
  free A-system.
- **(U) universal at the origin:** a computable `R_U` such that every radius-`r` pattern that
  occurs in `y_A` somewhere occurs at some `g` with `r < |g| ≤ R_U(r)`.

**Theorem.** Under (H) and (U), `Γ = A * Z` carries a nonempty subshift with decidable
language (hence effectively closed) on which `Γ` acts minimally and freely. That is (M2)
for `Γ`.

**Construction.**
- *Tree.* The Bass–Serre tree `T` has vertices the right cosets `Aμ` and `Bμ`, and edges
  the elements `μ ∈ Γ`, with `μ` joining `Aμ` and `Bμ`.
  - `R_λ: μ ↦ μλ` is a tree automorphism, and `Γ` acts freely on edges.
  - The star of `Aμ` is `Aμ`. Cayley steps `μ ↦ sμ` stay in one star: an A-star for
    `s ∈ S_A`, a B-star for `s = b^{±1}`. So Cayley paths project to walks in `T`.
- *Pointer, height, labels.* Fix a computable end `ξ_0` of `T`.
  - Every vertex `w` has a parent edge `p(w)`, the edge of its star toward `ξ_0`. Its
    Busemann height `h(w)` satisfies `h(parent) = h − 1`.
  - Fix a Sturmian subshift `Y_S ⊆ {0,1}^Z` with computable irrational slope, and
    `t_0 ∈ Y_S`. Every vertex is labelled `t_0(h(w))`.
- *Rooted fibers.*
  - At an A-vertex `w`, every edge is uniquely `a·p(w)` with `a ∈ A`; give it the fiber
    label `y_A(a)`.
  - At a B-vertex, `b^j·p(β)` gets `y_B(j)`, with `y_B` a Sturmian point (it satisfies (H)
    and (U), being uniformly recurrent).
- *The point.* `x(μ)` records:
  - which endpoint of `μ` is nearer `ξ_0`;
  - the Sturmian labels of both endpoints;
  - the A-fiber and B-fiber labels of `μ`.

  `x` is computable: reduced normal forms in `A*B` are computable from the word problem of
  `A`. Put `X := cl(Γ·x)`.

**Step 1: every radius-r pattern of x is Φ(T, W, P).**
- *The region.* Let `E = B(r)μ`. The vertices meeting `E` form a subtree, since Cayley paths
  project to walks. It has a unique vertex `w_top` nearest `ξ_0`, which is an ancestor of all
  the others.
- *Parent edges of the other vertices are in `E`.* For `w ≠ w_top`, a Cayley path inside `E`
  from `E ∩ star(w)` to `E ∩ star(w_top)` must cross the tree edge `p(w)`, i.e. pass through
  the edge `p(w)`. So `p(w) ∈ E`, and every `ε ∈ E ∩ star(w)` is `a·p(w)` with `|a| ≤ 2r`.
  - Hence all pointers, relative heights and fiber labels of `w ≠ w_top` are determined by
    the abstract ball `B(r)` and the position `T` of `w_top` in it.
  - `p(w_top) ∉ E`, since otherwise the parent of `w_top` would meet `E`.
- *The data.* So the pattern at `μ` is a computable function `Φ(T, W, P)` of:
  - `T`: which vertex of the abstract ball is the top (finitely many choices);
  - `W ∈ L(Y_S)`: the Sturmian word at heights `h(w_top), …, h(w_top)+2r+1`;
  - `P`: the radius-`2r` pattern of `y_A` (or `y_B`) at the offset `o` with `ε_0 = o·p(w_top)`,
    for a fixed reference edge `ε_0 ∈ E ∩ star(w_top)`.

**Step 2: every admissible (T, W, P) occurs within R(r) of every edge, with R computable.**
- *Target.* Given `μ'` and an admissible `(T, W, P)` (type-compatible `T`, `W ∈ L(Y_S)`,
  `P ∈ L_{2r}(y_A)`):
  - `μ'` is the parent edge of its endpoint `w_0` farther from `ξ_0`;
  - descending one generator step at a time (`p(u) ↦ c·p(u)`, `c ∈ S_A ∪ {b^{±1}}`, `c ≠ 1`) reaches vertices of every larger height.
- *Height.* By uniform recurrence of `Y_S` with parity (the slope is irrational, so so is
  twice it), within `d ≤ R_S(2r+2)` steps we reach `u` of the type of `T` with `W` at the
  heights `h(u), …, h(u)+2r+1`.
- *Offset.* By (U), `P` occurs in `y_A` at some `o'` with `2r < |o'| ≤ R_U(2r)`. Put
  `ν := σ_T^{-1}·o'·p(u)`, where `σ_T ∈ B(r)` is the abstract position of the reference edge.
- *Check.* `p(u)` is at distance `≥ |o'| − r > r` from `ν`, so `u` is the top of `B(r)ν`.
  - The top fiber there is `P`, the Sturmian window is `W`, and everything below is rooted
    exactly as in the target.
  - `d(μ', ν) ≤ d + R_U(2r) + r =: R(r)`.
- So `x` is uniformly recurrent with computable modulus, and `X` is minimal.
- The language `L_r(X) = L_r(x) = {Φ(T,W,P)}` is decidable, because
  `L_{2r}(y_A) = {patterns of y_A at |g| ≤ R_U(2r)}` is computable by (U). Also `X` is
  infinite, since the action is free (Step 3) and `Γ` is infinite.

**Step 3: freeness.**
- *Two types of points.* Every `z ∈ X` has pointer data of one of two types. The closed
  conditions "at most one parent edge per vertex" and "pointers along any path point toward
  a single vertex of the path" pass to limits.
  - (E): toward an end `ξ`.
  - (S): toward a sink vertex `v`, all of whose edges point in.
- *Labels in `X`.* In both cases:
  - Sturmian labels are functions of height, and their words lie in `L(Y_S)`;
  - fibers of non-sink vertices are exactly `y_A` / `y_B` rooted at the parent edge (closed,
    local conditions);
  - the fiber `f(a) = z(aμ_0)` at an A-sink `v = Aμ_0` is a limit of translates of `y_A`, so
    `f ∈ O_A`.
- *Setup.* Let `λ·z = z` with `λ ≠ 1`. Then `R_λ` preserves the pointer structure.
  - (E): `R_λ` fixes `ξ` and shifts heights by a constant `k`. In (E) heights take every
    integer value, and the labels are `t(h)` with `t ∈ Y_S` aperiodic, so `k = 0`. The rays
    from `u` and `R_λu` to `ξ` then merge at equal heights, so `R_λ` fixes a vertex on them
    and the edge from it toward `ξ`. Edge stabilizers are trivial, so `λ = 1`.
  - (S): `R_λ` fixes `v = Aμ_0`, so `a_0 := μ_0λμ_0^{-1} ∈ A∖{1}`. Then
    `z(aμ_0λ) = z(aa_0μ_0)`, so `a_0·f = f`, contradicting freeness of `O_A` (H). B-sinks
    work the same way with the aperiodic `y_B`. ∎

**Remarks.**
- (U) is a property of one position of one point, and (H) is freeness of its orbit closure.
  Neither involves minimality or recurrence anywhere else in `A`. Every point of an (M2)
  system for `A` has both, so the hypothesis is formally weaker than (M2) for `A`.
- *Honest scope.* For a point that is already centrally repetitive, (U) is equivalent to the
  global modulus. So the gain here is not that the seam problem disappears. The gain is
  that repetitivity is no longer required, and the seams can all be concentrated near one
  position (`decidable-groups-have-universal-hyperaperiodic-points`).
- The same proof works for `A * B` with any `B` that has such a point.
- The whole minimality burden is carried by two things: the Sturmian heights, and the
  "rooted fibers below, one free top" rigidity of the Bass–Serre tree.

**Lesson for general BH.** Minimality, the part of (M2) that every attempt on main
(Zorn, greedy towers, local lemma) failed to make effective, can be manufactured by passing
from an envelope `Λ_0` to `Λ_0 * Z`. That group is still finitely presented with solvable word problem
and still contains the input. A single tree-rooted fiber is exposed at far offsets only
at the top vertex of any ball, so recurrence reduces to universality of one point at one
position. The remaining obligation, (U)+(H) for `Λ_0`, is local, with no uniform recurrence.
This is a non-profinite skeleton, the replacement that
`effectively-rf-groups-have-effective-minimal-free-subshifts` says the simple inputs need.
