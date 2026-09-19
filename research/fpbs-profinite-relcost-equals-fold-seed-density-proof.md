---
rg: 2
id: fpbs-profinite-relcost-equals-fold-seed-density-proof
kind: route
title: Chords over a level fold to the Schreier graph exactly when E_K plus chords generate, clopen approximation turns any cheap graphing into level chords, chords are counted by 2-of-3 seeds, and the Sanov 3-adic expander tower is weakly above Bernoulli
target: fpbs-profinite-relcost-equals-fold-seed-density
requires:
  - fpbs-word-chords-are-dominated-by-merges
  - fpbs-mal-profinite-fold-density-is-finite-percolation
  - fpbs-strongly-ergodic-actions-have-fold-seed-floor
  - fpbs-mal-promotion-cost-monotone-under-weak-containment
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - fpbs-mal-floor-iff-deep-promotion-floor
  - fpbs-bernoulli-fold-seeds-have-density-at-least-2-25
artifacts:
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/sanov_gap.py
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/sanov_gap_out.txt
---

Notation is as in the target. `L` acts on the right. `Q` is a finite transitive
`L`-set with `n = |Q|`. An action `X` *has factor* `Q` when there is an
equivariant `π : X → Q`. Then `π_*μ` is uniform, since `Q` is transitive.

- A *piece* `(g, A)`, with `g ∈ L` and `A ⊆ X`, is the partial map
  `x ↦ x·g` on `A`, and it costs `μ(A)`. Every graphing inside `E_{X|L}`
  splits into countably many pieces with the same total cost.
- A *chord* `(p, w)`, with `p ∈ Q` and `w ∈ L`, is the piece
  `(w, π^{-1}(p))`, and it costs `1/n`.
- `G(Φ)` is the labelled graph over `Q` with real vertices `Q`, an `a`-edge
  `p → p·a`, a path labelled `c` from `p` to `p·c`, and, for each chord
  `(p, w)` of a finite set `Φ`, a path labelled `w` from `p` to `p·w`. Its
  fold is `F(Φ)`. The fold of `G(∅)` is `Γ_Q^K` of
  [[fpbs-word-chords-are-dominated-by-merges]], and
  `F(Φ) = fold(Γ_Q^K ∪ chord paths)`.
- `d(Q)` is the least `|Φ|` with `F(Φ)` having exactly `n` vertices. Item 4
  of [[fpbs-word-chords-are-dominated-by-merges]] gives `d(Q) = r(Q)`.

This route re-derives the folding criterion and the clopen approximation. The
same two steps appear in the main-checkout node
`fpbs-profinite-relcost-equals-relative-rank-gradient` (w14), which is not in
this worktree. They are proved here in full so that nothing depends on it.

## 1. Folding criterion

Let `ψ : V(G(Φ)) → Q` send each vertex to the point under it. Every edge
labelled `l` goes from a vertex over `y` to a vertex over `y·l`. Two edges
folded together have the same label and the same origin, so their ends lie
over the same point, and `ψ` descends to `F(Φ)`. Two standard facts:

- **(F1)** Every path in `F(Φ)` between the classes of two vertices `v, v'` of
  `G(Φ)` lifts to a path in `G(Φ)` from `v` to `v'` whose label is freely equal
  to the original. Induct on folds: when `e_1 : u → v_1` and `e_2 : u → v_2`
  are folded, insert `e_1^{-1} e_2` wherever the path passes from `v_1` to
  `v_2`.
- **(F2)** In a folded graph, a path whose label freely reduces to `w` is
  homotopic rel endpoints to the path reading the reduced word `w`.

**Real-to-real paths act.** Let `x ∈ π^{-1}(p)`, and let `γ` be a path in
`G(Φ)` from the real vertex `p` to a real vertex, with label `u`.
- Cut `γ` at its visits to real vertices. Interior vertices of `c`-paths and
  chord paths have degree 2.
- So each segment is an `a`-edge, a whole `c`-path, or a whole chord path,
  traversed in either direction. Otherwise the segment goes in and comes back
  out, and its label is freely trivial.
- Apply the segments in turn to `x`. The current point `z` satisfies
  `π(z) = ` the current real vertex. So each chord step is applied inside its
  domain `π^{-1}(p')`, or, backwards, inside its range `π^{-1}(p'·w)`.
- Hence `x·u ∈ [x]_{E_K ∨ Φ}`.

**Sufficiency (no freeness).** Suppose `F(Φ)` has `n` vertices.
- `ψ` is onto, and real vertices lie over distinct points. So the real
  vertices are all of `F(Φ)`.
- The first edge `p -b->` of the `c`-path at `p` becomes an edge `p -b-> p·b`
  of `F(Φ)`.
- By (F1), `G(Φ)` has a path from `p` to `p·b` with label freely equal to `b`.
- So `x·b ∈ [x]_{E_K ∨ Φ}` for every `x`. With `x·a ∈ E_K`, this gives
  `E_K ∨ Φ = E_L` on every action with factor `Q`.

**Necessity (freeness).** Suppose `E_K ∨ Φ = E_L` on one essentially free
action `X` with factor `Q`.
- Every `p` has mass `1/n > 0`, so some `x` over `p` is a free point with a
  finite `E_K ∨ Φ`-path from `x` to `x·b`.
- Each step is `a^{±1}`, `c^{±1}`, or a chord step taken at a point over its
  base (forwards) or over its target (backwards). So the steps trace a path in
  `G(Φ)` from `p` to a real vertex.
- Let `g` be the product of the step labels. Then `x·g = x·b`, so `g = b` by
  freeness.
- By (F2), `F(Φ)` has an edge `p -b->` ending at a real vertex. That vertex
  lies over `p·b`, so it is `p·b`. The `a`-edges are already present. So each
  real vertex carries all four labels `a^{±1}, b^{±1}`, each leading to a real
  vertex.
- Every vertex of `G(Φ)` is joined to a real vertex. If a non-real vertex
  existed, some non-real `v` would be adjacent in `F(Φ)` to a real `p` by a
  label `l`. But `p` already has its `l`-edge to the real `p·l`, and `F(Φ)` is
  folded, so `v = p·l`. This is a contradiction, so `F(Φ)` has `n` vertices.

**Consequence.** For essentially free `X` with factor `Q`, a finite set `Φ` of
level-`Q` chords satisfies `E_K ∨ Φ = E_L` iff `F(Φ)` has `n` vertices. So
`|Φ| ≥ d(Q) = r(Q)`.

## 2. Upper bound: relC(X) ≤ σ_b(X)

Let `X = lim Q_m` be profinite, with `π_m : X → Q_m`.
- Fix `m`, and take a set `Φ_m` of `d(Q_m)` chords with `F(Φ_m)` having
  `|Q_m|` vertices.
- By §1 sufficiency, pulled back through `π_m`, they give
  `E_K ∨ Φ_m = E_L` on `X`, at cost `d(Q_m)/|Q_m|`.
- So `relC(X) ≤ d(Q_m)/|Q_m| = r(Q_m)/|Q_m|` for every `m`.
- By (P) of [[fpbs-mal-profinite-fold-density-is-finite-percolation]],
  `inf_m r(Q_m)/|Q_m| = σ_b(X)`. Hence `relC(X) ≤ σ_b(X)`.

Freeness is not used here.

## 3. Lower bound: relC(X) ≥ σ_b(X) for essentially free X

Let `X = lim Q_m` be essentially free. The level-`m` cylinders `π_m^{-1}(p)`
form an `L`-invariant partition, since `π_m` is equivariant. Clopen sets are
finite unions of cylinders, and they are dense in the measure algebra.

**Patterns.** Let `Φ = {(g_i, A_i)}_{i ≥ 1}` be pieces with `E_K ∨ Φ = E_L`.
A *pattern* is a finite sequence of steps.
- Each step is `a^{±1}`, `c^{±1}`, a piece `(g_i, A_i)` taken forwards, or a
  piece taken backwards.
- The product of the step labels is `b` in `L`.
- The *pattern set* is the set of `x` at which every step is defined along
  the way. A forward piece needs the current point in `A_i`. A backward piece
  needs it in `A_i·g_i`.
- If the pattern uses pieces from a finite set `I`, then its pattern set is a
  finite intersection of sets `A_i·h` and `A_i·g_i·h`. Here `i ∈ I`, and `h`
  runs over the inverses of the finitely many prefix products of the pattern.

Every `x` in a pattern set has `(x, x·b) ∈ E_K ∨ Φ`.

Conversely, take a free point `x` whose pair `(x, x·b)` is joined by a finite
`E_K ∨ Φ`-path. Almost every point is such a point. Let `g` be the product of
the path's step labels. Then `x·g = x·b`, so `g = b` by freeness. So the
path's step sequence is a pattern, and `x` lies in its pattern set. Hence the
pattern sets cover `X` up to a null set.

**Truncate.** Fix `ε > 0`, and choose `Φ` with `C(Φ) < relC(X) + ε`.
- There are countably many patterns. By countable additivity, some finite
  set `P` of patterns, using pieces from a finite set `I`, has pattern sets
  covering a set `G_0` with `μ(G_0) ≥ 1 − ε`.
- Let `R` bound the lengths of the patterns in `P`. Then every pattern set in
  `P` is an intersection of at most `R` translates of sets `A_i` or `A_i·g_i`,
  with `i ∈ I`.

**Approximate.** Take `δ > 0`. Choose `m`, and clopen sets `A_i'` of level `m`
for `i ∈ I`, with `μ(A_i Δ A_i') < δ`.
- Translation preserves `μ`, and `(A_i·h) Δ (A_i'·h) = (A_i Δ A_i')·h`.
- Define `G_0'` from the `A_i'` by the same patterns. Each pattern set moves
  by at most `Rδ`, so `μ(G_0 Δ G_0') ≤ R|P|δ`.
- Each `A_i'·h` is a union of level-`m` cylinders, because the cylinder
  partition is invariant. So `G_0'` is a union of level-`m` cylinders.

**The chord graphing.** Put `B = X \ G_0'`, which is also a union of level-`m`
cylinders, and

```text
Φ'  =  { (g_i, A_i') : i ∈ I }  ∪  { (b, B) } .
```

- Every `x ∈ G_0'` lies in a pattern set computed from the `A_i'`, so
  `(x, x·b) ∈ E_K ∨ Φ'`.
- Every `x ∈ B` has `(x, x·b) ∈ Φ'`.
- So `E_K ∨ Φ' = E_L`.
- Each piece of `Φ'` is a union of level-`m` chords: `(p, g_i)` over the
  cylinders `p ⊆ A_i'`, and `(p, b)` over the cylinders `p ⊆ B`. So `Φ'` is a
  finite set of `N = |Q_m|·C(Φ')` level-`m` chords.
- By §1 necessity, applied to the essentially free `X`,
  `N ≥ d(Q_m) = r(Q_m)`.

**Conclude.**

```text
r(Q_m)/|Q_m|  ≤  C(Φ')  ≤  Σ_{i∈I} μ(A_i) + |I|δ + μ(B)
              ≤  C(Φ) + |I|δ + ε + R|P|δ .
```

Choose `δ` with `(|I| + R|P|)δ < ε`. Then
`σ_b(X) = inf_m r(Q_m)/|Q_m| < relC(X) + 3ε`. Since `ε` is arbitrary,
`σ_b(X) ≤ relC(X)`. With §2, `relC(X) = σ_b(X)`, which is item 1. ∎

**Where freeness is used.** Twice: to know that the path from `x` to `x·b`
reads `b`, and in §1 necessity. For profinite actions that are not free, only
`relC ≤ σ_b` survives.

## 4. The Sanov 3-adic witness and D0 (item 2)

Put `A = [[1,2],[0,1]]` and `B = [[1,0],[2,1]]`, and let `Λ = <A, B> ≤ SL_2(Z)`.

**(a) Freeness.** By Sanov's theorem (1947), `A` and `B` generate a free group
of rank 2. So `θ : L → SL_2(Z)`, `a ↦ A`, `b ↦ B`, is injective. Compose with
the embedding `SL_2(Z) ↪ SL_2(Z_3)`, and let `L` act on `X = SL_2(Z_3)` by
`x·g = x θ(g)`.
- This is free at every point: `x θ(g) = x` forces `θ(g) = 1`, so `g = 1`.
- It preserves Haar measure, since `SL_2(Z_3)` is compact and hence unimodular.

**(b) Profinite with transitive levels.** Put `Q_k = SL_2(Z/3^k)`, with `L`
acting by right multiplication through `θ` mod `3^k`. Then
`X = lim_k Q_k`, Haar measure is the inverse limit of the uniform measures,
and the reductions are equivariant. Transitivity of `Q_k` means that the
image `Λ_k` of `Λ` in `SL_2(Z/3^k)` is the whole group.
- `Γ(2) = ±Λ`. The two matrices generate a subgroup of `Γ(2)`, and the
  classical description of `Γ(2)` as `{±1} × Λ` gives equality.
- Reduction mod `3^k` is onto from `Γ(2)`, by the Chinese remainder theorem.
  `SL_2(Z) → SL_2(Z/2) × SL_2(Z/3^k)` is onto, and `Γ(2)` is the preimage of
  `1 × SL_2(Z/3^k)`.
- So `Λ_k` has index at most 2 in `SL_2(Z/3^k)`.
- Index 2 is impossible. Such a subgroup would give a surjection
  `SL_2(Z/3^k) → Z/2`. That surjection kills the kernel of reduction to
  `SL_2(F_3)`, which is a 3-group, so it factors through `SL_2(F_3)`. But
  `SL_2(F_3) = Q_8 ⋊ Z/3` has abelianization `Z/3`, so it has no quotient
  `Z/2`.
- Hence `Λ_k = SL_2(Z/3^k)`, and `Q_k` is transitive.

`sanov_gap.py` confirms transitivity for `k ≤ 3`.

**(c) Uniform spectral gap.** The Schreier graph of `Q_k` is the Cayley graph
of `SL_2(Z/3^k)` with respect to `A^{±1}, B^{±1}`. It is the quotient of `Λ`
by the congruence subgroup `Λ ∩ Γ(3^k)`.
- `Λ` has finite index in `SL_2(Z)`. By Selberg's `3/16` theorem, `SL_2(Z)`
  has property `(τ)` with respect to congruence subgroups, and `(τ)` passes to
  finite-index subgroups (Lubotzky, *Discrete Groups, Expanding Graphs and
  Invariant Measures*, 1994, Ch. 4).
- Independently, Bourgain and Gamburd prove that Cayley graphs of
  `SL_2(Z/p^n)` with respect to the reduction of any fixed finite set that
  generates a Zariski-dense subgroup of `SL_2(Z)` form an expander family as
  `n → ∞` (*Expansion and random walks in `SL_d(Z/p^n Z)`: I*, J. Eur.
  Math. Soc. 10 (2008), 987–1011). That applies to `p = 3` and `{A, B}`,
  since `Λ` is free of rank 2 and hence Zariski dense.
- So `λ* := sup_k λ_2(Q_k) < 1`, where
  `λ_2` is the second largest eigenvalue of `M = (a + a^{-1} + b + b^{-1})/4`.

The computed values are `λ_2 = 0.6830, 0.7938, 0.8687` for `k = 1, 2, 3`
(`sanov_gap_out.txt`). They are evidence only, and no explicit value of `λ*`
is claimed.

**(d) The floor.**
- `L^2_0(X)` is the closure of the union of the level-`k` mean-zero functions.
  So `ρ_X = sup_k λ_2(Q_k) = λ* < 1`.
- Theorem S of [[fpbs-strongly-ergodic-actions-have-fold-seed-floor]], in its
  profinite form, gives `σ_b(X) ≥ (1 − λ*)/4 > 0`.
- By item 1, `relC(X) = σ_b(X) > 0`.
- By [[abert-weiss-free-actions-weakly-contain-bernoulli]], the Bernoulli
  shift `ρ` of `L` is weakly contained in the free action `X`.
- Theorem M of [[fpbs-mal-promotion-cost-monotone-under-weak-containment]],
  with `H' = K`, `H = L = <K, b>`, `a = ρ` free and `b = X`, gives
  `relC(X) = P(X; K, L) ≤ P(ρ; K, L) = relC(ρ) = Q_0`.

The same argument applies to every essentially free profinite `X`, with the
Abért–Weiss step and Theorem M unchanged. This gives
`Q_0 ≥ sup_X σ_b(X) ≥ (1 − λ*)/4 > 0`, which is item 2.

`Q_0` is the depth-0 term of [[fpbs-mal-floor-iff-deep-promotion-floor]], so
(D0) holds. ∎

## 5. Consequences (items 3 and 4), and what is left

**Item 3.** Both `ρ` and the Sanov action `X` are free p.m.p. actions of `L`,
and `K` is a nontrivial finitely generated subgroup, with `rk K = rk L = 2`.
- By §4, `relC(X) > 0` and `relC(ρ) = Q_0 > 0`.
- The claim `fpbs-relative-fixed-price-free-pairs` asserts
  `relC ≤ (rk L − rk K)^+ = 0` for every free action. So it is false.
- Gaboriau's fixed price for free groups gives
  `C(E_{X|L}) = C(E_{X|K}) = 2`, since `E_{X|K}` is the orbit relation of a
  free action of the rank-2 free group `K`. So the right-hand side of
  `fpbs-relative-fixed-price-fg-pairs` is also `0` at these actions, and that
  claim fails in its free-pair case.

**Item 4.** Suppose `X` is essentially free, profinite and weakly contained in
`ρ`. Then `σ_b(X) ≥ 2/25` by
[[fpbs-bernoulli-fold-seeds-have-density-at-least-2-25]]. Item 1 and §4 then
give `Q_0 ≥ relC(X) = σ_b(X) ≥ 2/25`.
- Weak containment passes to Koopman representations (Kechris). So such an
  `X` would have a tempered Koopman representation on `L^2_0`, and its levels
  would satisfy `λ_2(Q_n) ≤ √3/2`.
- No such tower is known, so item 4 stays conditional.

**What is left: (D1).** By [[fpbs-mal-floor-iff-deep-promotion-floor]], the
open target is `inf_j Q_j(ρ) > 0`, where
`Q_j = P(ρ; L_{j+1}, L_j)` allows labels anywhere in `L`. The method above
does not reach `j ≥ 1`. The obstruction is precise.

- **Finite form at depth j.** Over a level `Q`, let `Γ_j` be the fold of the
  `L_{j+1}`-coset graph: `a`-edges and `t_{j+1}`-paths. Attach `k` chords
  with labels in `L`, and fold, to get `H`. Success means that reading
  `t_j = φ^j(b)` from every real `p` stays inside `H` and ends at `p·t_j`.
- **Normal form.** §1 of the route
  `fpbs-word-chords-are-dominated-by-merges-proof` still applies with base
  `Γ_j`. It shows that `H` is `Γ_j / cl(P)`, with `|P| = m`, together with a
  part carrying no vertex of `Γ_j` (the Δ-part), whose excess
  `E_Δ − V_Δ ≥ 0` is at most `k − m`.
- **Why depth 0 closes.** At `j = 0` the target `t_0 = b` is one letter. Every
  success graph has only real vertices, so the Δ-part is empty and `k ≥ m`
  counts merges only.
- **Where it breaks.** At `j ≥ 1` the `t_j`-reading from `p` may leave
  `V(Γ_j)` and run through the Δ-part. One Δ-bridge of excess 1 can carry the
  `t_j`-readings of many base points. So the count `k ≥ m` no longer bounds a
  seed number of the depth-`j` problem.
- **The step to prove for (D1).** At each depth `j`, the `t_j`-readings
  through the Δ-part can be rerouted inside `Γ_j / cl(P')` with
  `|P'| ≤ C(|P| + excess)`, for a constant `C` independent of `j`.

This is the finite-level form of survivor P3. It can fail on its own.
