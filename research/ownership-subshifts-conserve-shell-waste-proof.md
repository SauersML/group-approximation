---
rg: 2
id: ownership-subshifts-conserve-shell-waste-proof
kind: route
title: Counting claims across a shell, plus Mendelsohn–Dulmage, rules out strong irreducibility for full ownership and arrow shifts
target: ownership-subshifts-conserve-shell-waste
requires: []
artifacts:
  - experiments/ownership-sft-si-2026-09-17/shell_waste_check.py
  - experiments/ownership-sft-si-2026-09-17/shell_waste_check.out
---

## Why sufficient

The notation is that of the target. Claims use right multiplication (`g -> g s`), and the SI separation
uses `E_1 K`. Both are compatible with the left action: `h(E_1 K) ∩ h E_2 = h(E_1 K ∩ E_2)`, and a
translate `(h.o)` of an ownership point has claim set `h · (claims of o)`, with the claims of `v` in
`h.o` equal to `h ·` (claims of `h^(-1) v` in `o`). Enlarging `K` keeps SI, so assume `e ∈ K`.

1. **Both shifts are SFTs.**
   - `o ∈ Own(S,k)` iff at every `g` the tuple `o(g)` has distinct entries, and for every `h ∈ g S S^(-1)`
     with `h ≠ g` no claim of `h` equals a claim of `g`. A collision `g s = h s'` forces `h ∈ g S S^(-1)`.
     So these are finite-window conditions.
   - `X_S` has window `S^(-1)`, as recorded in `nonamenable-groups-carry-arrow-shift-strict-automata`.

2. **Shell-waste identity (item 1).** Take `Q`, `T`, `W` as in the target. If `g s_i(g) = t ∈ T`, then
   `g = t s_i(g)^(-1) ∈ T S^(-1) ⊆ Q ∪ W`. So every claimer of a vertex of `T` lies in `Q` or in `W`.
   - Every claim of `q ∈ Q` lies in `QS ⊆ T`, which gives `k|Q|` pairs `(q,i)`.
   - Claims are pairwise distinct, because `(g,i) -> g s_i(g)` is injective.
   - So the number of claimed vertices of `T` is `k|Q| + #{(w,i) : w ∈ W, w s_i(w) ∈ T}`, which gives the
     formula for `u_o(T)`.

   The arrow case is the same count. The arrows landing in `T` come from `T S^(-1) ⊆ Q ∪ W`, and all
   `|Q|` arrows from `Q` land in `QS ⊆ T`. So `Σ_{t ∈ T} indeg(t) = |Q| + #{w ∈ W : wφ(w) ∈ T}`, and
   subtracting `2|T|` gives `e_φ(T)`. In both formulas the only point-dependent term is read from the
   point on `W`.

3. **Dichotomy (item 2).** Suppose some `x_2 ∈ Y` has an unclaimed vertex `h_0`. Fix any `x_1 ∈ Y` and
   `g ∈ G`.
   - Replace `x_2` by its translate `(g h_0^(-1)).x_2 ∈ Y`, in which `g` is unclaimed.
   - Put `Q = g V^2`, `T = g V^3` and `W = g V^4 \ g V^2`. Then `QS ⊆ gV^3 = T` and `T S^(-1) ⊆ g V^4`, so
     `W ⊇ T S^(-1) \ Q` and `W ∩ Q = ∅`.
   - Put `E_1 = W` and `E_2 = g V`. If `w k = g v` with `w ∈ W`, `k ∈ K` and `v ∈ V`, then
     `w = g v k^(-1) ∈ g V^2`, which is impossible. So `E_1 K ∩ E_2 = ∅`.
   - SI gives `y ∈ Y` with `y = x_1` on `W` and `y = x_2` on `gV`.
   - The claimers of `g` in any point lie in `g S^(-1) ⊆ gV`. So whether `g` is claimed is read from the
     point on `gV`, and `g` is unclaimed in `y`. Since `g ∈ T`, `u_y(T) ≥ 1`.
   - By step 2, `u_{x_1}(T) = u_y(T) ≥ 1`, because `x_1` and `y` agree on `W`. So `x_1` has an unclaimed
     vertex in `g V^3`.

   The arrow version is the same argument. The sources of arrows into `g` lie in `g S^(-1) ⊆ gV`, so
   `indeg_y(g) = indeg_{x_2}(g) ≥ 3`. Every summand of `e_y(T)` is at least 0 because `y ∈ X_S`, so
   `e_y(T) ≥ 1`. Then `e_{x_1}(T) = e_y(T) ≥ 1`, so some `t ∈ g V^3` has `indeg_{x_1}(t) ≥ 3`.

4. **Mendelsohn–Dulmage, in the form used here.** Let `Γ` be a bipartite graph with sides `L` and `R`.
   Suppose `M_1` is a matching covering every vertex of `L` and `M_2` is a matching covering every vertex
   of `R`. Then `Γ` has a perfect matching.

   *Proof.* In the multigraph `M_1 ∪ M_2`, with an edge in both counted twice, every vertex has degree 1
   or 2, since it meets at most one edge of each matching and at least one of them. Each component is one
   of the following:
   - a doubled edge;
   - a finite cycle;
   - a two-way infinite path;
   - a one-way infinite path (ray);
   - a finite path.

   Along a path the edges alternate between `M_1` and `M_2`. A degree-1 vertex in `L` has only its
   `M_1`-edge, and a degree-1 vertex in `R` has only its `M_2`-edge. So a finite path is impossible:
   - an `L`-to-`L` path has even length, but it starts and ends with `M_1`-edges;
   - an `R`-to-`R` path has even length, but it starts and ends with `M_2`-edges;
   - an `L`-to-`R` path has odd length, but it starts with an `M_1`-edge and ends with an `M_2`-edge.

   An alternating path of even length starts and ends with different types, and one of odd length starts
   and ends with the same type. That is the contradiction in all three cases. A one-vertex component has
   degree 0, which is excluded.

   Now take `M_1` on doubled edges, cycles, two-way paths and rays whose endpoint lies in `L`. Take `M_2`
   on rays whose endpoint lies in `R`.
   - On the first three kinds, every vertex has degree 2, so `M_1` covers it.
   - On a ray, every vertex except the endpoint has degree 2. The endpoint's only edge belongs to the
     matching chosen for that ray.

   The components are disjoint, so the union of these choices is a perfect matching. The choice is made
   separately in each component and needs no choice principle. ∎

5. **Item 3, ownership.** Let `e ∈ S` and `o' ∈ Own(S,k+1)`.
   - **A wasteful point.** Dropping the last slot gives `o ∈ Own(S,k)`. The vertex `g s_{k+1}(g)` was
     claimed in `o'` only by `(g, k+1)`, by injectivity. So it is unclaimed in `o`.
   - **A perfect point.** Let `L = G × [k]` and `R = G`, with `(g,i) ~ h` iff `h ∈ gS`.
     - `M_1 = {(g,i) -- g s_i(g)}` is a matching covering `L`.
     - `M_2 = {(h,1) -- h}` is a matching covering `R`. It is an edge set of `Γ` because `h = h e ∈ hS`.
     - Step 4 gives a perfect matching `μ`. Setting `s_i(g) = g^(-1) μ(g,i) ∈ S` defines a point of
       `Own(S,k)`, since `μ` is injective on `L`. Every vertex is claimed, since `μ` is onto `R`.
   - So `Own(S,k)` has a perfect point and a point with an unclaimed vertex. Step 3 fails for it, so it is
     not SI.

6. **Item 3, arrows.** Let `φ ∈ X_S`, with `e ∈ S`.
   - Let `L = G` (sources) and `R = G × [2]` (slots), with `g ~ (h,j)` iff `h ∈ gS`.
   - Fix an enumeration of `G`. Let `p_1(h), p_2(h)` be the first two `g` with `gφ(g) = h`.
     `M_2 = {p_j(h) -- (h,j)}` is a matching covering `R`. A source `g` has one target, so it determines
     `h`, and `j` is then determined because `p_1(h) ≠ p_2(h)`.
   - `M_1 = {g -- (g,1)}` is a matching covering `L`.
   - Step 4 gives a perfect matching `μ`. The map `g -> first coordinate of μ(g)` is `g φ_0(g)` for an
     exact `φ_0 ∈ X_S`, since each fibre is `{μ^(-1)(h,1), μ^(-1)(h,2)}`.
   - So if `X_S` also has a point with an indegree of at least 3, step 3 fails and `X_S` is not SI.
   - For `S^2`, let `X_S` be nonempty and `f = f_{φ_0}`. The fibres of `f ∘ f` have size 4, being disjoint
     unions of two fibres of size 2. Also `f(f(g)) = g φ_0(g) φ_0(gφ_0(g)) ∈ g S^2`. So `f ∘ f` is a point
     of `X_{S^2}` with indegree 4, while `φ_0 ∈ X_S ⊆ X_{S^2}` is exact, because `S ⊆ S^2`.
   - The same two points lie in `X_{S'}` for every symmetric `S' ⊇ S^2`. By item 1 of
     `nonamenable-groups-carry-arrow-shift-strict-automata`, some `X_{S_0}` is nonempty on every
     nonamenable group.

7. **Item 4.** In `F_2` every `w ≠ e` has one parent and three children, and `e` has four children.
   - "Each `w` claims three of its children" is a point of `Own(B_1,3)`, because claims by distinct
     vertices are distinct children. Step 5 then applies with `k = 2`.
   - "Each `w ≠ e` points to its parent and `e` to itself" has indegree 3 off `e` and 5 at `e`. It lies in
     `X_{B_1}`, and step 6 applies.
   - `shell_waste_check.py` builds an explicit perfect point of `Own(B_1,2)` and runs the finite gluing
     test.
     - A vertex of type `s` claims itself and its first child.
     - A vertex of type `f`, claimed by its parent, claims two children.
     - Unclaimed children are of type `s`.

8. **Item 5.** Suppose `o ∈ Own(S,k)` has a finite orbit. Its stabilizer has finite index, so it contains a
   finite-index normal subgroup `N`, and `o(ng) = o(g)` for `n ∈ N`.
   - Map `(gN, i)` to `g s_i(g) N`. This is well defined: `(ng) s_i(ng) N = n g s_i(g) N = g s_i(g) N`, using
     `o(ng) = o(g)` and then the normality of `N`.
   - It is injective. Suppose `g' s_j(g') = g s_i(g) n`. Since `N` is normal, `g s_i(g) n = n' g s_i(g)`
     for some `n' ∈ N`, and `n' g s_i(g) = (n'g) s_i(n'g)`. Injectivity of claims gives `g' = n'g` and
     `j = i`.
   - So `G/N × [k]` injects into `G/N`, which is impossible for `k ≥ 2` since `G/N` is finite.

9. **Item 6.** Let `π` have memory `M`, a finite set with `π(x)(g)` determined by `x` on `gM`. Suppose `X`
   is SI with constant `K_X`. Take `π(x_1), π(x_2)` and finite `E_1, E_2` with
   `E_1 K ∩ E_2 = ∅`, where `K = M K_X M^(-1)`.
   - Then `E_1 M K_X ∩ E_2 M = ∅`.
   - SI of `X` gives `x` agreeing with `x_i` on `E_i M`.
   - Then `π(x)` agrees with `π(x_i)` on `E_i`.

   So `π(X)` is SI with constant `K`. It is a subshift of `Own(S,k)` or of `X_S`, so step 3 applies to it.
