---
rg: 2
id: thompson-t-quad-complete-laminations-diagonal-proof
kind: route
title: An invariant mean would give both diagonals of a quad the same mean, by nested moves, while exactly one of them is present at every point
target: thompson-t-quad-complete-laminations-carry-no-invariant-mean
requires: []
---

Notation is as in the target claim. All arcs are open arcs of `S^1`, and `cl` denotes closure.
Write `F_{A,B} = f_{A,B} ∘ π`, a `{0,1}`-valued function on `X`. Call a pair `(A, B)` of
nonempty arcs **separated** if `cl A ∩ cl B = ∅`. Since `f_{A,B} = f_{B,A}`, pairs are
unordered.

**Step 0: `T` is transitive on cyclically ordered dyadic 4-tuples.** Let `p_1 < p_2 < p_3 < p_4`
and `p'_1 < p'_2 < p'_3 < p'_4` be cyclically ordered dyadic points.
- By Step 0 of `lifted-thompson-t-convex-line-walls-contraction-proof`, each closed arc
  `[p_i, p_{i+1}]` (indices mod 4) has an increasing PL map onto `[p'_i, p'_{i+1}]`. These maps
  have dyadic breakpoints and power-of-2 slopes.
- The four maps agree at the shared endpoints. Glued, they give an element `g ∈ T` with
  `g p_i = p'_i`.

**Step 1: equivariance.**
- `T` preserves `D`, the crossing relation and the cyclic order. It maps quads to quads, and
  `f_{A,B}(g·τ) = f_{g^{-1}A, g^{-1}B}(τ)`. So `Tri_D` is `T`-invariant.
- Equivariance of `π` gives `F_{A,B}(g x) = F_{g^{-1}A, g^{-1}B}(x)`.

**Step 2: sharp exclusivity.** Fix a quad `a < b < c < d` and a point `x`, and put `τ = πx`.
- At least one of `F_{I_1,I_3}(x)` and `F_{I_2,I_4}(x)` is `1`, by quad-completeness.
- At most one is `1`. A chord `{p, q}` with `p ∈ I_1`, `q ∈ I_3` and a chord `{u, v}` with
  `u ∈ I_2`, `v ∈ I_4` have cyclic order `p < u < q < v`, so they cross.

So `F_{I_1,I_3} + F_{I_2,I_4} = 1` and `|F_{I_1,I_3} − F_{I_2,I_4}| = 1`, pointwise on `X`.

Quad points are required to lie outside `D` so that quad-completeness is a sensible
condition. A chord ending at a quad point lies in none of the open arcs. For example, `τ_0`
fails the condition at quads with dyadic corners.

**Step 3: `ν` is constant on separated pairs.** Let `m` be a `T`-invariant mean on `ℓ^∞(X)`,
and put `ν(A,B) = m(F_{A,B})`.
- *Invariance.* By Step 1, `ν(g^{-1}A, g^{-1}B) = m(F_{A,B} ∘ g) = ν(A,B)`.
- *Dyadic pairs.* A separated pair of arcs with dyadic endpoints is `((p_1,p_2), (p_3,p_4))`
  for a cyclically ordered dyadic 4-tuple. By Step 0, `ν = κ` on all such pairs, for one
  constant `κ`.
- *All pairs.* Let `(A, B)` be separated. Choose separated dyadic pairs `(A^−, B^−)` and
  `(A^+, B^+)` with `A^− ⊆ A ⊆ A^+` and `B^− ⊆ B ⊆ B^+`. This is possible because the dyadics
  are dense and `cl A`, `cl B` are disjoint closed arcs. Monotonicity of `f` in each argument
  gives `F_{A^−,B^−} ≤ F_{A,B} ≤ F_{A^+,B^+}`. Positivity of `m` gives `κ ≤ ν(A,B) ≤ κ`.

**Step 4: nested moves cost nothing.** Let `(A', B')` be separated, with `A ⊆ A'`, `B ⊆ B'` and
`A, B` nonempty. Then `(A, B)` is separated, and `F_{A',B'} − F_{A,B}` takes values in
`{0, 1}`. So `m|F_{A',B'} − F_{A,B}| = ν(A',B') − ν(A,B) = κ − κ = 0`.

**Step 5: the chain.** Fix a quad `a < b < c < d`. Choose points `b < b' < c' < c` and
`d < d' < a' < a`, and consider five nested moves, each between a separated pair and a
separated pair containing or contained in it:

| pair | arcs | relation to the previous pair |
|---|---|---|
| `P_0` | `(a,b)`, `(c,d)` | this is `(I_1, I_3)` |
| `P_1` | `(a,b)`, `(b',d)` | contains `P_0`, since `b' < c` |
| `P_2` | `(a,b)`, `(b',c')` | contained in `P_1` |
| `P_3` | `(d',b)`, `(b',c')` | contains `P_2`, since `d' < a` |
| `P_4` | `(d',a')`, `(b',c')` | contained in `P_3`, since `a' < b` |
| `P_5` | `(d,a)`, `(b,c)` | contains `P_4`; this is `(I_4, I_2)` |

Separation holds at every step:
- `P_1`: `[a,b]` and `[b',d]` are disjoint, since `b < b'` and `d < a`.
- `P_3`: `[d',b]` and `[b',c']` are disjoint, since `b < b'` and `c' < d'`.
- `P_5`: `[d,a]` and `[b,c]` are disjoint.
- `P_0`, `P_2` and `P_4` are contained in these, so they are separated too.

By Step 4 and the triangle inequality for the seminorm `h ↦ m|h|`,
`m|F_{I_1,I_3} − F_{I_2,I_4}| ≤ Σ_{i=1}^{5} m|F_{P_i} − F_{P_{i−1}}| = 0`.
By Step 2 the left side is `m(1) = 1`. This is a contradiction, and it proves Part 1.

Step 2 also gives `2κ = 1`, but that is not needed.

**Step 6: the measurable case (Part 2).** Let `ξ_n` be almost invariant unit vectors for the
Koopman representation `ρ`, `(ρ(g)ξ)(x) = ξ(g^{-1}x) · (d(g_*μ)/dμ)(x)^{1/2}`.
- Then `|ρ(g)ξ|² μ = g_*(|ξ|² μ)`, so `∫ (F ∘ g) |ξ_n|² dμ = ∫ F |ρ(g)ξ_n|² dμ` for
  `F ∈ L^∞(X, μ)`.
- `‖ |ρ(g)ξ_n|² − |ξ_n|² ‖_1 ≤ ‖ρ(g)ξ_n − ξ_n‖_2 · ‖ρ(g)ξ_n + ξ_n‖_2 ≤ 2‖ρ(g)ξ_n − ξ_n‖_2 → 0`.
- Hence every weak* cluster point `m` of the states `F ↦ ∫ F |ξ_n|² dμ` is a mean on
  `L^∞(X, μ)` with `m(F ∘ g) = m(F)` for all `g ∈ T`.

Steps 1 to 5 go through for this `m` with "pointwise" replaced by "μ-a.e.":
- equivariance holds a.e. for each of the countably many `g`;
- monotonicity and the identity of Step 2 hold a.e.;
- a mean on `L^∞` is positive and satisfies `m(1) = 1`.

The same contradiction follows, which proves Part 2.

**Remark (endpoint sets that depend on the point).** Let `Tri_ctbl` be the `T`-invariant set of
non-crossing chord sets `τ` with countable endpoint set `E(τ)` that are quad-complete for every
quad avoiding `E(τ)`. Suppose `π : X → Tri_ctbl` is equivariant a.e., each `F_{A,B}` is
measurable, and `{(x,t) : t ∈ E(πx)}` is measurable in `X × S^1`. Then Part 2 still holds.
- Take a probability `μ'` equivalent to `μ`. Each `x`-section of that set is countable, so by
  Fubini, `μ'{x : t ∈ E(πx)} = 0` for Lebesgue-a.e. `t`.
- Choose one quad `a < b < c < d` of such points. Step 2 then holds a.e. for this quad.
- Steps 3 to 5 never use that the other arc endpoints avoid `E`. Step 3 uses dyadic arcs,
  Steps 4 and 5 use only monotonicity, and `f_{A,B}` is defined for all open arcs.

**Step 7: finite lemma.** Let `P` be a convex polygon triangulated by its sides and a maximal
set of non-crossing diagonals. Suppose its vertices are split into four cyclically consecutive
blocks `B_1, B_2, B_3, B_4`, with `B_1` and `B_3` nonempty. Then some edge of the triangulation
joins `B_1` to `B_3` or joins `B_2` to `B_4`.

*Proof.* Take `u ∈ B_1` and `w ∈ B_3`. If `uw` is an edge, we are done. Otherwise:
- The segment `uw` crosses diagonals `e_1, …, e_k` in order, with `k ≥ 1`. It passes through
  triangles `t_0 ∋ u`, …, `t_k ∋ w`, where `t_{i−1}` and `t_i` share the side `e_i`.
- Let `L` be the vertices strictly between `u` and `w` on the side containing `B_2`, and `R`
  the vertices on the side containing `B_4`. Each `e_i = l_i r_i` has `l_i ∈ L ⊆ B_1 ∪ B_2 ∪ B_3`
  and `r_i ∈ R ⊆ B_3 ∪ B_4 ∪ B_1`.
- Suppose no `e_i` joins opposite blocks. Then the block pair `(l_i, r_i)` of each `e_i` is
  one of `(1,1)`, `(1,4)`, `(2,1)`, which touch `B_1` and not `B_3` (**type 1**), or one of
  `(2,3)`, `(3,3)`, `(3,4)`, which touch `B_3` and not `B_1` (**type 3**).
- `t_0 = u l_1 r_1`. If `e_1` had type 3, it would have a vertex `v ∈ B_3`, and the side `uv`
  of `t_0` would be an edge from `B_1` to `B_3`. So `e_1` has type 1. By symmetry at `w`,
  `e_k` has type 3.
- So some `e_i` has type 1 and `e_{i+1}` has type 3. They are two sides of `t_i`, so they
  share a vertex `s`. The block of `s` touches both types, so `s` lies in `B_2` or `B_4`.
  - If `s ∈ B_2`, then `s = l_i = l_{i+1}`. The pairs are `(2,1)` and `(2,3)`, so `r_i ∈ B_1`
    and `r_{i+1} ∈ B_3`. The third side `r_i r_{i+1}` of `t_i` joins `B_1` to `B_3`.
  - If `s ∈ B_4`, then `s = r_i = r_{i+1}`. The pairs are `(1,4)` and `(3,4)`, so the third
    side `l_i l_{i+1}` joins `B_1` to `B_3`.

In every case some edge joins opposite blocks. ∎

**Step 8: `τ_0 ∈ Tri_D` (Part 3).**
- *Endpoints.* All endpoints of chords of `τ_0` are dyadic.
- *Non-crossing.* The chord `{k/2^n, (k+1)/2^n}` bounds the dyadic arc
  `[k/2^n, (k+1)/2^n]`. Two dyadic arcs are nested or have disjoint interiors, so their chords
  do not cross.
- *Triangulation at level `n`.* Fix `n ≥ 2` and let `D_n = 2^{−n}Z/Z`, which has `2^n` points.
  The level-`n` chords are the `2^n` sides of the convex `2^n`-gon on `D_n`. The chords of
  levels `1, …, n−1` are distinct diagonals. Their number is `1 + 2² + ⋯ + 2^{n−1} = 2^n − 3`,
  because at level 1 the arcs `[0,1/2]` and `[1/2,1]` give the same chord. A non-crossing set
  of `N − 3` diagonals of an `N`-gon is maximal, so this is a triangulation.
- *Quad-completeness.* Let `a < b < c < d` be non-dyadic. Choose `n ≥ 2` with `D_n` meeting
  all four arcs `I_j`. The blocks `B_j = D_n ∩ I_j` are nonempty, cyclically consecutive, and
  partition `D_n`. Step 7 gives a chord of `τ_0` from `I_1` to `I_3` or from `I_2` to `I_4`.
- *Translates.* For `g ∈ T`, `g·τ_0 ∈ Tri_D` by Step 1.

**Step 9: subgroups (Part 4).**
- Let `H ≤ T` fix `τ ∈ Tri_D`. The map `π : T/H → Tri_D`, `gH ↦ g·τ`, is well defined and
  equivariant. Co-amenability of `H` is exactly the existence of a `T`-invariant mean on
  `ℓ^∞(T/H)`, and Part 1 excludes it.
- The question-mark function `?` conjugates the action of `PSL_2(Z)` on `RP^1 = R ∪ {∞}`
  into `T`. It sends the Farey tessellation (the `PSL_2(Z)`-orbit of the chord `{0, ∞}`) to
  `τ_0`, because `?` sends a Farey mediant to the midpoint of the images. This is the standard
  identification of `T` with the piecewise-`PSL_2(Z)` group of Imbert, Lochak–Schneps and
  Thurston.
- So `? PSL_2(Z) ?^{−1} ≤ Stab_T(τ_0)`, and Part 4 follows for its conjugates in `T` and their
  subgroups.
- Parts 1 to 3 do not depend on this identification.
