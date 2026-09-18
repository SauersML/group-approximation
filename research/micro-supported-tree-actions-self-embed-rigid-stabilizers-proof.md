---
rg: 2
id: micro-supported-tree-actions-self-embed-rigid-stabilizers-proof
kind: route
title: Hyperbolic axes inside every half-tree push any half-tree into any other, and two opposite rays of one axis give disjoint copies
target: micro-supported-tree-actions-self-embed-rigid-stabilizers
requires: []
---

The notation is that of the target. Automorphisms of `T` are identified with
their actions, since the action is faithful. `π_L` is the nearest-point projection
to a line `L`.

**0. Standard facts.**

- **(F0) Half-trees.** Any two half-trees `X`, `Y` with distinct underlying edges
  satisfy one of `X ⊆ Y`, `Y ⊆ X`, `X ∩ Y = ∅` or `X ∪ Y = T`. If `f''` follows
  `f'` along a line `L`, with the same orientation, then `Y_{f''} ⊆ Y_{f'}`. For
  `γ ∈ Γ`, `γY_f = Y_{γf}` and `γR(Y)γ^{-1} = R(γY)`. An element of `R(Y_f)` fixes
  `x` and every neighbour of `x` except possibly `y`, so it fixes `y` too, and it
  preserves `Y_f`.
- **(F1) Disjoint supports.** Let subgroups `H_i ≤ R(Z_i)` have pairwise disjoint
  `Z_i`. Take `g ∈ H_i`, `k ∈ H_j` with `i ≠ j` and a vertex `z`. If `z ∈ Z_i`,
  then `kz = z` and `gz ∈ Z_i`, so `kgz = gz = gkz`. The case `z ∈ Z_j` is
  symmetric, and otherwise both fix `z`. So the `H_i` commute. A finite product
  `h_1 ⋯ h_m` acts on `Z_i` as `h_i`. If it is trivial, each `h_i` is trivial on
  `Z_i` and off it, so `h_i = 1` by faithfulness. Hence `⟨H_i⟩ = ⊕ H_i`.
- **(F2) Classification** (Tits 1977; Culler--Morgan 1987, §2). Suppose `Γ` acts
  without inversions, fixes no end and is minimal on a tree that is not a single
  vertex or a line. Then `Γ` contains hyperbolic elements, and two of them have
  axes with no common end.
- **(F3) Union of axes** (Culler--Morgan 1987, Prop. 3.1). For a minimal action
  with a hyperbolic element, `T` is the union of the axes of hyperbolic elements.
- **(F4) Projections.** A subtree `S` disjoint from a line `L` has
  `π_L(S) = {q}` for a single vertex `q`. If `h` is hyperbolic with axis `L`, then
  `π_L(h^n S) = {h^n q}`.

**1. Lemma A: every half-tree contains a hyperbolic axis.** Let `Y = Y_f`,
`f = (x, y)`.

- By (F3), `f` lies on the axis `L` of a hyperbolic `g`. Replacing `g` by `g^{-1}`,
  `g` translates `L` from `x` toward `y`. Let `ξ_±` be its attracting and
  repelling ends.
- By (F2), not every hyperbolic axis contains `ξ_−`. Take a hyperbolic `k` whose
  axis `A_k` does not end at `ξ_−`.
- `A_k ∩ L` is empty, a finite segment, or a ray toward `ξ_+`. In each case
  `π_L(A_k)` is bounded in the direction of `ξ_−`. Pick an edge `f'` of `L`,
  oriented toward `ξ_+`, lying strictly on the `ξ_−` side of `π_L(A_k)`. Then
  `A_k ⊆ Y_{f'}`.
- For large `n`, `g^n f'` lies on `L` beyond `f`, with the same orientation. By
  (F0), `g^n A_k ⊆ Y_{g^n f'} ⊆ Y_f`.
- So `g^n k g^{-n}` is hyperbolic with axis inside `Y`.

**2. Lemma B: transport.** Let `X`, `Y` be half-trees.

- **Case (i): `X ⊆ Y`.** Take `γ = 1`.
- **Case (ii): `Y ∩ X^c` contains a half-tree `Z`.**
  - By Lemma A, take a hyperbolic `h` with axis `A ⊆ Z`.
  - `X` and `Y^c` are subtrees disjoint from `A`, so by (F4) `π_A(X) = {q}` and
    `π_A(Y^c) = {q'}`.
  - Pick `n ≠ 0` with `h^n q ≠ q'`. A vertex of `h^n X ∩ Y^c` would project to
    both `h^n q` and `q'`. So `h^n X ⊆ Y`.
- **Case (iii): `Y ⊊ X`.**
  - The pair `(X, X^c)` is in case (ii), since `X^c ∩ X^c = X^c` is a half-tree.
    So some `γ_1 X ⊆ X^c ⊆ Y^c`.
  - Then `γ_1 X ∩ Y = ∅`, so `Y ∩ (γ_1 X)^c = Y`, and the pair `(γ_1 X, Y)` is in
    case (ii). This gives `γ_2 γ_1 X ⊆ Y`.
- **Coverage.** By (F0), these cases cover all pairs: `X ∩ Y = ∅` and
  incomparable `X ∪ Y = T` fall under (ii). If the underlying edges coincide,
  then `X = Y` (case (i)) or `X = Y^c` (case (ii)).

Now `γX ⊆ Y` gives `γR(X)γ^{-1} = R(γX) ≤ R(Y)`. Taking `X = Y_0` from (N) gives
`R(Y) ≠ 1` for every `Y`. This proves item 1.

**3. Disjoint half-trees and self-embedding.**

- By Lemma A, let `A ⊆ Y` be the axis of a hyperbolic element. `Y^c` is a subtree
  disjoint from `A`, so `π_A(Y^c) = {q_0}`.
- Choose an edge `f_1` of `A` with both endpoints strictly on one side of `q_0`,
  oriented away from `q_0`. Choose `f_2` likewise on the other side. Put
  `Z_i = Y_{f_i}`.
- Every vertex `z ∈ Z_i` has `π_A(z) ∈ Z_i ∩ A`, which does not contain `q_0`. So
  `Z_i ∩ Y^c = ∅`, that is `Z_i ⊆ Y`. The two half-trees point away from each
  other along `A`, so `Z_1 ∩ Z_2 = ∅`.
- Repeat inside `Z_2` to get disjoint `Z_{21}, Z_{22} ⊆ Z_2`, and so on. The
  half-trees `Z_1, Z_{21}, Z_{221}, ...` are pairwise disjoint and lie in `Y`.
- By Lemma B, pick `γ_i` with `γ_i Y ⊆ Z_i` for each of them. Then
  `R(γ_i Y) ≅ R(Y)`, these subgroups lie in `R(Z_i) ≤ R(Y)`, and by (F1) they
  generate `⊕_i R(γ_i Y) ≅ ⊕_N R(Y)` inside `R(Y)`.
- If `R(Y)` were finite, `R(Y) ⊇ R(Y)^2` would force `R(Y) = 1`, which contradicts
  item 1.

This proves item 2.

**4. Items 3 and 4.**

- Take `h ≠ 1` in `R(Y)`. Replace it by a power, so that it has infinite order or
  prime order `p`. Its copies in the factors of `⊕_N R(Y)` generate `⊕_N ⟨h⟩`.
- `R(Y) ≤ Γ_f ≤ Γ⁺` for the underlying edge `f` of `Y`, by (F0).
- In a group whose finite subgroups have order at most `b`, `(Z/p)^{b}` cannot
  embed. In a group whose free abelian subgroups have rank at most `b`, `Z^{b+1}`
  cannot embed. A non-finitely-generated abelian `⊕_N ⟨h⟩` cannot lie in a group
  whose abelian subgroups are all finitely generated.
- For the named classes: finite groups are clear. Hyperbolic groups have finitely
  many conjugacy classes of finite subgroups and no `Z^2`.
- **Finite vcd.** Let `H_0 ≤ H` be torsion-free of finite index with
  `cd H_0 = d`. Finite subgroups meet `H_0` trivially, so their order is at most
  `[H : H_0]`. `Z^k ∩ H_0` is free abelian of rank `k`, so `k ≤ d`.
- **Proper cocompact CAT(0) groups.** Finitely many conjugacy classes of finite
  subgroups (Bridson--Haefliger II.2.8). Flats of dimension at most the geometric
  dimension, via the flat torus theorem.

**5. Item 5.**

- Suppose `Fix(N) ≠ 1` for the `(k−1)`-neighbourhood `N` of an edge `f`, and
  `Fix(N) = Fix(N ∪ Y_f)·Fix(N ∪ Y_{f̄})`. Then one of the two factors is
  nontrivial.
- `Fix(N ∪ Y_{f̄})` fixes every vertex outside `Y_f`, so it lies in `R(Y_f)`.
  Symmetrically `Fix(N ∪ Y_f) ≤ R(Y_{f̄})`. So (N) holds.
- For `k = 1`, `N` is the pair of endpoints of `f`. `Fix(N) = Γ_f`, and
  `Fix(N ∪ Y_f) = Fix(Y_f)` by (F0), so the condition is Tits' (P).
- The groups `Γ⁺ ⊇ Γ_f` and `Γ^{+k} ⊇ Fix(N)` contain rigid stabilizers, hence
  `⊕_N ⟨h⟩` by item 3. ∎

**What is not claimed.** Nothing here uses finite presentability or local
finiteness. Thompson-like and branch groups do contain `⊕_N R` inside `R`, so this
kills only bounded-rank hosts, not the Tits route as a whole.
