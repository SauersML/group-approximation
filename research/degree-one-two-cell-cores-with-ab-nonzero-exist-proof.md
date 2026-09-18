---
rg: 2
id: degree-one-two-cell-cores-with-ab-nonzero-exist-proof
kind: route
title: Proof of the fiber-product criterion for ratio pairs of w-loops, of the length-16 degree-one two-cell core with (a,b) = (1,2), and of its non-admissibility via the character x -> 2, y -> -1
target: degree-one-two-cell-cores-with-ab-nonzero-exist
requires:
  - two-cell-core-deletions-need-a-unit-fox-coefficient
  - core-relation-elimination-bounds-relative-defect
  - non-proper-power-one-relator-complexes-are-aspherical
artifacts:
  - experiments/two-cell-fiber-product-2026-09-18/example_check.py
  - experiments/two-cell-fiber-product-2026-09-18/cover3.py
  - experiments/two-cell-fiber-product-2026-09-18/lowindex.g
  - experiments/two-cell-fiber-product-2026-09-18/RESULTS.md
---

Notation is as in the claim. A folded `S`-graph has at most one edge with each label leaving and
entering each vertex. So a word read from a given vertex determines its path.

## (A) Fiber-product criterion

The fiber product `Γ ×_S Γ` has vertex set `V(Γ)^2`. It has an `s`-edge `(p, q) → (p', q')` whenever
`p → p'` and `q → q'` are `s`-edges of `Γ`. It is folded.

**Off-diagonal.** Suppose some path labelled `σ` joins `(v_0, v_1)` to a diagonal vertex `(u, u)`.
Then reading `σ^{-1}` from `u` is deterministic, so it ends at `v_0` and at `v_1` alike. Hence
`v_0 = v_1`. So a component containing `(v_0, v_1)` with `v_0 ≠ v_1` has no diagonal vertex. On a
diagonal component `p_1 = p_2`, so `p_{2*} h = λ p_{1*} h ≠ 0` is impossible for `λ ≠ 1`.

**Closed paths.** A word `w` reads closed paths at `v_0` and at `v_1` iff it labels a closed path
`γ` at `(v_0, v_1)` in `Γ ×_S Γ`. The only-if direction uses that the two paths exist and are
determined by `w`. The paths it reads are `p_1 γ` and `p_2 γ`. Their cycles are therefore
`z_j = p_{j+1,*}[γ]`, where `[γ] ∈ H_1(Δ)`. This proves (i) ⇒ (ii) with `h = [γ]`.

**Converse.** Given `h`, the Hurewicz map is onto, so there is a closed path `γ` at a base vertex
`o ∈ Δ` with `[γ] = h`. Free reduction does not change `h`, and in a folded graph reduced paths have
reduced labels. Write the reduced loop as `γ = σ γ' σ^{-1}`, where `γ'` has a cyclically reduced
label and is based at the endpoint `(v_0', v_1')` of `σ`. Then `[γ'] = h ≠ 0`, so `γ'` is nonempty,
and `w = label(γ')` works at `(v_0', v_1')`.

**Commutator subgroup.** The rose map `ρ: Γ → R_S` satisfies `ρ p_1 = ρ p_2`. So
`ρ_* z_0 = ρ_* z_1 = λ ρ_* z_0`, which forces `ρ_* z_0 = 0`. This says that `w` has exponent sum
zero in every letter, that is, `w ∈ [F(S), F(S)]`. ∎(A)

## (B) The example

`w = x y^4 x^{-1} y^{-1} x y^2 x^{-1} y^{-5}` has length 16 and is cyclically reduced: it starts
with `x` and ends with `y^{-1}`. Its exponent sums are `x: 1-1+1-1 = 0` and `y: 4-1+2-5 = 0`. It is
not a proper power, since a period `d ∈ {1,2,4,8}` would force `w[1..8] = w[9..16]`, and
`x y y y y X Y x ≠ y y X Y Y Y Y Y`.

Take the spanning tree `0 -y-> 1 -x-> 2`. The non-tree edges give the basis
- `a = x` (the loop at 0),
- `b = y·y` (the edge `1 → 0`, closed by the tree),
- `c = (yx) y (yx)^{-1}` (the loop at 2).

These images generate `H`. Now read `w` letter by letter. Write `T` for a tree edge, and write the
basis letter for each non-tree edge (its inverse when crossed backwards).

- **From 0.** The path is
  `x:a | y:T→1 | y:b→0 | y:T→1 | y:b→0 | X:a^{-1} | Y:b^{-1}→1 | x:T→2 | y:c | y:c | X:T→1 |
  Y:T→0 | Y:b^{-1}→1 | Y:T→0 | Y:b^{-1}→1 | Y:T→0`.
  It is closed at 0, with `u_0 = a b b a^{-1} b^{-1} c c b^{-1} b^{-1}`.
- **From 1.** The path is
  `x:T→2 | y:c | y:c | y:c | y:c | X:T→1 | Y:T→0 | x:a | y:T→1 | y:b→0 | X:a^{-1} | Y:b^{-1}→1 |
  Y:T→0 | Y:b^{-1}→1 | Y:T→0 | Y:b^{-1}→1`.
  It is closed at 1. The tree path from 0 to 1 contributes no basis letter, so
  `u_1 = c^4 a b a^{-1} b^{-3}`.

Hence `[u_0] = (0, -1, 2) = p`, which is primitive, and `[u_1] = (0, -2, 4) = 2p`. `example_check.py`
redoes all of this mechanically.

Both loops read `w` itself, so `ε_0 = ε_1 = 1`. The labels of the tree paths are `t_0 = 1` and
`t_1 = y`, so `g = y`. The fundamental class `b e_0 - a e_1 = 2e_0 - e_1` is a 2-cycle. Once (C)
shows that `C` is a core, this gives the rest of (B):
- by `non-proper-power-one-relator-complexes-are-aspherical`, `X_H ≃ K(H,1)`, and
  `H_2(C) ⊂ H_2(X_H)` because both are 2-dimensional;
- the projection to `H_2(X) = Z` sends the class to `2 - 1 = 1`, so `H_2(H) → H_2(G)` is onto.

## (C) C is a core

**Step 1: an index-3 cover.** Let `x = (1 2)` and `y = (0 1)` act on the right on `{0,1,2}`.
Reading `w` from each of `0, 1, 2` returns to the start (`cover3.py`). So this is an action of `G`.
Let `K` be the stabilizer of `0`. Each generator of `H` fixes `0`, so `H ≤ K`.

`X_K` has vertices `0, 1, 2`, one `x`-edge and one `y`-edge leaving each vertex, and one lift of the
2-cell at each vertex (`w` is not a proper power). Its 1-skeleton is `Γ` plus the single edge
`f: 2 -x-> 1`. The lifts at `0` and `1` avoid `f`, so they are `e_0` and `e_1`. The lift at `2` is
`e_2`, which reads

`f x | y^4 | f X | Y | f x | y^2 | f X | Y^5`.

**Step 2: the vertices stay distinct.** The vertices of `Γ` go to the cosets `K, Ky, Kyx`. These are
distinct, because they act on `0` as `0, 1, 2`. So the lift `C → X_H` is injective on vertices,
hence on edges, since an edge is determined by its origin and label. The 2-cells `e_0, e_1` sit at
distinct vertices. Thus `C` is a subcomplex of `X_H` and of `X_K`. `lowindex.g` independently finds
108 subgroups of index at most 8 that contain `H` and separate the three vertices.

**Step 3: presentations.** Put `A = π_1(C, 0) = ⟨a, b, c | u_0, u_1⟩`. From `u_1`,
`a b a^{-1} = c^{-4} b^3`. Then `a b^2 a^{-1} = (a b a^{-1})^2 = c^{-4} b^3 c^{-4} b^3`, so modulo
`u_1`, `u_0` becomes

`r_L = c^{-4} b^3 c^{-4} b^2 c^2 b^{-2}`.

So `A = ⟨L, a | a b a^{-1} = c^{-4} b^3⟩`, where `L = ⟨b, c | r_L⟩`.

Now add `f`. Put `τ_1 = y` and `τ_2 = yx` (tree paths) and `φ = τ_2 f τ_1^{-1}`. Rebase `e_2` at `0`
through `τ_2`. Then `y^4` at vertex 1 is `b^2`, `y^2` at 1 is `b`, and `y^{-1}` at 2 is `c^{-1}`.
This gives

`r_2 = φ b^2 φ^{-1} c^{-1} φ b φ^{-1} c^{-5}`,

and van Kampen gives `K = π_1(X_K) = ⟨L, a, φ | a b a^{-1} = c^{-4} b^3, r_2⟩`. Since `r_2` does not
involve `a`,

`K = ⟨M, a | a b a^{-1} = c^{-4} b^3⟩`, where `M = (L * ⟨φ⟩) / ⟨⟨r_2⟩⟩`.

**Step 4: L.** The relator `r_L` is cyclically reduced: it starts with `c^{-1}` and ends with
`b^{-1}`. It has length 17 and exponent sums `(b, c) = (3, -6)`. A proper power `u^k` would need
`k | 3` and `k | 17`, so `r_L` is not one. Hence the following hold.
- `L` is torsion-free and locally indicable (Brodskii; Howie).
- `b ≠ 1` and `c ≠ 1` in `L` (Magnus's Freiheitssatz: `r_L` involves both letters).
- `c^{-4} b^3 ≠ 1` in `L`: in `L^ab = Z^2 / ⟨(3, -6)⟩` its image `(3, -4)` is nonzero.

So `⟨b⟩` and `⟨c^{-4} b^3⟩` are infinite cyclic, and `A` is an HNN extension of `L`.

**Step 5: L embeds in M.** In `L * ⟨φ⟩`, `r_2` is cyclically reduced of syllable length 8. Its
`L`-syllables `b^2, c^{-1}, b, c^{-5}` are nontrivial, so `r_2` is not conjugate into a factor. The
Freiheitssatz for one-relator products of locally indicable groups (Brodskii 1984; Howie 1981,
*On pairs of 2-complexes and systems of equations over groups*) then gives that `L → M` is
injective.

**Step 6: A embeds in K.** Both `A` and `K` are HNN extensions with the same stable letter and the
same associated subgroups `⟨b⟩ ≅ ⟨c^{-4} b^3⟩ ≤ L ≤ M`. These stay infinite cyclic in `M` by
Step 5.

Take a Britton-reduced word of `A`, meaning one with no pinch `a ℓ a^{-1}` with `ℓ ∈ ⟨b⟩` and no
pinch `a^{-1} ℓ a` with `ℓ ∈ ⟨c^{-4} b^3⟩`. It stays Britton-reduced in `K`. Membership of an
element `ℓ ∈ L` in `⟨b⟩` or in `⟨c^{-4} b^3⟩` does not change when `L` is viewed inside `M`, because
`L → M` is injective. By Britton's lemma for `K`, the natural map `A → K` is injective.

**Conclusion.** `K ≤ G` has index 3 and `A → K` is the map induced by `C ⊂ X_K`. So `π_1(C) → G` is
injective with image `H`. Hence `C ⊂ X_H` induces `π_1(C) ≅ H`, and `C` is a two-cell core. ∎(C)

## (D) The character

`χ(x) = 2`, `χ(y) = -1` is a homomorphism `G → Q^*`, since `w ∈ [F,F]`. On the basis, `χ(a) = 2`,
`χ(b) = 1`, `χ(c) = -1`, and `χ(g) = -1`. Fox derivatives are evaluated as `∂_x(u)^χ`. An
occurrence of `x` adds `χ(prefix)`, and an occurrence of `x^{-1}` subtracts
`χ(prefix · x^{-1})`.

- **u_0 = a b b a^{-1} b^{-1} c c b^{-1} b^{-1}.** The prefix values after each letter are
  `2, 2, 2, 1, 1, -1, 1, 1, 1`. This gives `∂_a = 1 - 1 = 0`, `∂_b = 2 + 2 - 1 - 1 - 1 = 1` and
  `∂_c = 1 + (-1) = 0`.
- **u_1 = c c c c a b a^{-1} b^{-1} b^{-1} b^{-1}.** The prefix values are
  `-1, 1, -1, 1, 2, 2, 1, 1, 1, 1`. This gives `∂_a = 1 - 1 = 0`, `∂_b = 2 - 1 - 1 - 1 = -1` and
  `∂_c = 1 - 1 + 1 - 1 = 0`.

So `c^χ = εχ(g) ∂u_0^χ - ∂u_1^χ = -(0,1,0) - (0,-1,0) = 0`.

If `Σ_x c_x d_x = 1` held in `ZG`, applying the ring map `ZG → Q` induced by `χ` would give
`0 = 1`. So `c` is not unimodular, and by (U2) of `two-cell-core-deletions-need-a-unit-fox-coefficient`,
`pd_{ZG} I_{G/H} ≥ 2`. Unimodularity and the vanishing of `c^χ` do not depend on the basis `B`,
because a change of basis multiplies `c` by an invertible Jacobian over `ZH`.

The factorization `c^ab = f(s)·(…)` quoted in the claim is the output of `abel.py` and
`example_check.py` (the latter in a spanning-tree basis). It shows that `c` also vanishes on the
whole curve `s^3 = s^2 + 1`. ∎
