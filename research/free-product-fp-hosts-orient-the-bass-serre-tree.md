---
rg: 2
id: free-product-fp-hosts-orient-the-bass-serre-tree
kind: claim
title: A finitely presented minimal crossed product over a free product orients the Bass–Serre tree toward one sink sheet or one ray, its sheets must record the exit, and the end-space crossed product over a free product with a one-ended factor is not finitely presented
distinct_from:
  boundary-crossed-product-is-a-leavitt-path-algebra: that is the finitely presented end-space host over F_d = Z * ... * Z; part 6 here shows the same construction fails as soon as one free factor is one-ended.
  free-group-cantor-crossed-products-are-not-universal-hosts: that kills free acting groups by word-problem complexity; this is a structural constraint over free products with one-ended factors, where no complexity kill is available.
---

**ESTABLISHED (unreviewed).** Graph note: this node imports part 1 of `fp-crossed-products-force-connected-differences` and refines `fp-minimal-crossed-products-map-onto-ends` (both ESTABLISHED on main). They are named in the body only, because this worktree's base predates them. The ends node gives an equivariant map onto `Ends(P)` over any multi-ended group and stops at free products with one-ended factors. This node works edge by edge in the Bass–Serre tree, and the cut edge replaces the ball of the connectivity theorem.

Let `P = Q_1 * Q_2` with `Q_1`, `Q_2` nontrivial and finitely
generated, with generating set `S = S_1 ⊔ S_2` (`S_i` a finite symmetric generating set of `Q_i`)
and word metric `d(g, h) = |g^(-1) h|`. Let `k` be a field, `X ⊆ A^P` an infinite minimal subshift,
and suppose `B_X = LC(X, k) ⋊ P` is finitely presented. Let `n` be a relator length from part 1 of
`fp-crossed-products-force-connected-differences`. Let `r >= 1` be a window radius with
`X = {x : (g^(-1) x)|B_r ∈ L_(B_r)(X) for all g}` (`fp-crossed-products-force-sft-over-any-group`).
Put `R = max(2r, n)`.

**Sides.** For `h ∈ P` let `W_i` be the elements whose normal form begins with a nontrivial `Q_i`
syllable, and `side_i(h) = h W_i`. So `P = {h} ⊔ side_1(h) ⊔ side_2(h)`. In the Bass–Serre tree `T`
(vertices `gQ_1`, `gQ_2`, edge `g` joining them), `side_i(h)` is the set of edges other than `h` on the
`hQ_i` side of the edge `h`. For `x ∈ X` and `h ∈ P`, call a pattern `p ∈ L_(B_R(h))(X)`
*undetermined on* `C ⊆ P` if two points of `X` extending `p` differ somewhere in `C`.

1. **Exit dichotomy.** Every `p ∈ L_(B_R(h))(X)` is undetermined on exactly one of `side_1(h)`,
   `side_2(h)`. Call that index `σ(p)`. All extensions of `p` agree on `side_(3-σ(p))(h) ∪ B_R(h)`.
2. **Orientation.** For `x ∈ X`, orient each edge `h` of `T` toward the vertex `hQ_(τ_x(h))`, where
   `τ_x(h) = σ(x|B_R(h))`.
   - If `τ_x(h) = i` and `h' ∈ side_(3-i)(h)`, then `h'` points toward `h`.
   - Every vertex has at most one outgoing edge.
   - Exactly one of the following holds.
     - There is a unique *sink* vertex `v`, and every edge points toward `v`.
     - There is no sink, and all maximal outgoing paths define one common ray, whose end is `ξ_T(x) ∈ ∂T`.
   - `X_v = {x : v is the sink of x}` is closed. `X_(gv) = g X_v`, the sets `X_v` are pairwise
     disjoint, and `X_(Q_i)` is a `Q_i`-subshift.
3. **Determinism.**
   - (a) If `x ∈ X_v` with `v = gQ_i`, then `x` is the only point of `X` that agrees with `x` on the
     `R`-neighbourhood of the coset `gQ_i`.
   - (b) If the ray of `x` leaves the vertex `gQ_i` through the edge `h_0 ∈ gQ_i`, then `x|B_R(h_0)`
     determines `x` on `side_i(h_0) ∪ B_R(h_0)`. This set contains the whole sheet `gQ_i` and
     everything behind it. So for each exit `h_0` there are at most `|L_(B_R)(X)|` possible
     configurations there.
4. **Fibres.**
   - Each `X_v` has empty interior, so `X_V = ∪_v X_v` is meagre and the ray fibre `X_∂` is comeagre
     and nonempty.
   - If `Q_i` is infinite, then `X_(Q_i) ≠ ∅`, and `X_V` is dense.
5. **Sheets record the exit.** Suppose `x, y ∈ X_∂` have rays leaving the vertex `Q_1` through
   distinct edges `h ≠ h' ∈ Q_1`. Then the set `K = {q ∈ Q_1 : x|B_R(q) ≠ y|B_R(q)}` contains a
   chain from `B_R(h) ∩ Q_1` to `B_R(h') ∩ Q_1` with steps of length at most `2n` in `Q_1`.
6. **End-space kill.** Suppose `Q_1` is one-ended and `Q_2` is one-ended or infinite cyclic. Then
   `Ends(P)` is conjugate to a subshift. For every field `k`, `LC(Ends(P), k) ⋊ P` is **not**
   finitely presented.

**Why it matters.** Attempt 9 of `decidable-group-algebras-have-fp-cantor-crossed-hosts` left two
gaps: one-ended non-amenable `P`, and free products whose one-ended factors carry the free end inside
a sheet. This node settles the shape of the second gap.
- A host over `Γ * Z` or `Γ_1 * Γ_2` is a tree of sheet systems.
- Every point has a sink sheet or a ray.
- Everything off the sink sheet, or behind the current exit, is read from one `R`-ball.
- All remaining freedom lives in the `Q_i`-subshifts `X_(Q_i)` of sink configurations (3a).

**Killed class.** Any construction whose sheet decorations do not see which exit carries the ray
dies at part 5. The failing step is "two far exits on one sheet give a split difference set". This
class includes:
- the end-space host, the natural analogue of the finitely presented boundary Leavitt path algebra
  over `F_d` (part 6);
- "free tree extensions" of a sheet system in which the sheet configuration is chosen independently
  of the exit.

**Where it does not reach.**
- Part 5 is satisfiable in principle: a sheet may carry a pointer field toward its exit, for example
  sign fields over `Z^2`.
- It is not a complexity bound. So the free-product lane is not dead. It now needs a one-ended
  torsion-free Farrell–Jones factor `Γ` with a `Γ`-subshift of *exit-pointer* configurations, whose
  sink limits carry the hardness, inside a finitely presented crossed product.
- Over `F_d`, where the sheets are two-ended, part 5 is met by the boundary shift, and part 6's
  hypothesis fails.

Route: `free-product-fp-hosts-orient-the-bass-serre-tree-proof`.
