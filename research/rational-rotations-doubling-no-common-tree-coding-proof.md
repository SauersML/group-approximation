---
rg: 2
id: rational-rotations-doubling-no-common-tree-coding-proof
kind: route
title: Boundary points of tree vertices are pulled back by the covering map, so they have bounded odd denominators, and rotations by other rationals cannot move vertices to vertices
target: rational-rotations-and-doubling-have-no-common-tree-coding
requires: []
---

Lane proof, elementary, self-contained. Notation as in the claim. `π : D → R/Z` is the quotient
map; `μ` is Lebesgue measure pulled back along `π` (well defined, since `π` is injective off the
countable set `S`).

**Step 0. Boundaries.** For a clopen `C ⊆ D` put `∂C = {s ∈ S : exactly one of s^-, s^+ lies in C}`.
- Clopen sets of `D` are finite unions of basic arcs `[a^+, b^-]` (`a, b ∈ S`), so `∂C` is finite and
  `μ(C) > 0` when `C ≠ ∅`.
- If `∂C = ∅` then `C` is `π`-saturated, so `π(C)` and `π(D ∖ C)` are disjoint closed sets covering
  the connected `R/Z`. Hence **a nonempty proper clopen set has nonempty boundary.**
- `∂R_q(C) = ∂C + q`, since `R_q` sends `s^±` to `(s+q)^±`.
- For `C ⊆ D_i`: `β_i` sends `s^±` to `(d s)^±` for `s` interior to the piece, and the two ends of
  `D_i` go to `0`. So `∂C ⊆ {x : d x ∈ ∂β_i(C) ∪ {0}}`, and `μ(β_i C) = d μ(C)`.

Write `C_v = φ(∂T_v)` for the vertex set of a vertex `v`.

**Step 1. Every vertex boundary has bounded odd part.** By hypothesis there is a finite vertex
partition `P` of `D` on each piece `A` of which the relevant branch `β_i` is induced by a subtree
isomorphism `T_A ≅ T_A'`. Refining `P` (descendants of `A` map to descendants of `A'`), assume each
piece lies in a single `D_i`, so `β` below `P` is well defined.
- Let `U` be the finite set of vertices that are strict ancestors of pieces of `P`. Every other vertex
  is a descendant-or-equal of a unique piece.
- Take a vertex `C` not in `U`. Put `C_0 = C` and `C_(j+1) = β(C_j)` while `C_j ∉ U`. Each `C_(j+1)`
  is again a vertex set (the subtree isomorphism maps vertices to vertices), and
  `μ(C_(j+1)) = d μ(C_j)`. Since `μ <= 1`, the sequence stops at some `C_k ∈ U`.
- Iterating Step 0, `∂C ⊆ {x : d^k x ∈ E}`, where `E = {0} ∪ ⋃_(W ∈ U) ∂W`. (If `d y ∈ F ∪ {0}` and
  `d x ∈ {y} ∪ {0}` then `d^2 x ∈ d F ∪ {0}`, so the extra `0`s collapse.)
- `E` is a finite subset of `Q/Z`. Let `M` be the least common multiple of the parts of the
  denominators of elements of `E` that are coprime to `d`. If `d^k x ≡ e (mod 1)` with `e ∈ E`,
  the denominator of `x` divides `d^k` times that of `e`. So
  **every vertex boundary lies in `S_M = (1/M) Z[1/d] / Z`**, a subgroup of `Q/Z`. Vertices in
  `U` are covered because `∂W ⊆ E`.

**Step 2. Rotations.** Suppose `R_q` is `T`-almost-automorphic, via a finite vertex partition `P'`
with `R_q(A)` a vertex set for each `A ∈ P'`.
- If some `A ∈ P'` is proper, pick `e ∈ ∂A` (nonempty by Step 0). Then `e ∈ S_M` and
  `e + q ∈ ∂R_q(A) ⊆ S_M`, so `q ∈ S_M`.
- If `P' = {D}`, then `R_q` is induced by an automorphism of `T`, which maps a proper vertex (a child
  of the first vertex with at least two children) to a vertex, and the same argument applies.

So every almost-automorphic rotation has `q ∈ S_M`. For a prime `p ∤ dM`, `1/p ∉ S_M`. ∎

**Consequence for hosts.** Suppose `g ∈ H` acts on each piece `B = α_1 × … × α_n` of a finite box
partition as a product of prefix replacements, and preserves the fibration over coordinate `k`
with base map `ρ`. Then `ρ` agrees on `α_k` with the prefix replacement `α_k → α'_k`. Refining the
cones `α_k` to a partition shows that `ρ` is almost-automorphic for the binary tree of coordinate
`k`, transported to `D` by the chosen identification.
- Apply this to the elements with base maps `R_(1/p)`, and to the dilation with base map
  `R_(β_i) ∘ β_i` on `D_i`.
- The theorem needs one adjustment for a rotated branch `x ↦ d x + b_i`: Step 0 becomes
  `∂C ⊆ {x : d x + b_i ∈ ∂β'(C) ∪ {b_i}}`. Enlarge `E` by the finitely many `b_i` and their images
  under `x ↦ d x + b_j`, and `M` by the parts of their denominators coprime to `d`. (By the last bullet the rotation
  constant `b` is the same for every branch.) If some `b_i` is irrational
  the branch is not continuous on `D`.
- A skew product `δ` with `δ R_q δ^-1 = R_(dq)` for all `q` in a dense subgroup has a base map `ρ`
  with `ρ(x + q) = ρ(x) + d q`. So `ρ(x) − d x` is invariant under a dense group of rotations and
  continuous as a map to `R/Z`, hence constant: `ρ = R_b ∘ (x ↦ d x)` globally. That is why the
  base map has the form above.
- For `SV_G`: an element that is a skew product over coordinate `k` is locally induced by an
  element `w g` of `V ≀_S G` with `(w g)(x)_k = w_k(x_(g^-1 k))`. This depends only on `x_k` only if
  `g` fixes `k`, and then it is a prefix replacement of `x_k`.
