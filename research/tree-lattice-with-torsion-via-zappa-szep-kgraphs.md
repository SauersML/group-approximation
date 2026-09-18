---
rg: 2
id: tree-lattice-with-torsion-via-zappa-szep-kgraphs
kind: route
title: Replace the free cube k-graph by a transported one with the finite germ groupoid of cube stabilizers acting self-similarly, then run the power, phase and stabilization steps unchanged
target: cocompact-tree-product-lattices-lie-in-type-a-class
requires: [tree-lattice-kgraph-power-phase-proof, stabilized-kgraph-full-group-clopen-action-proof, virtually-torsion-free-tree-lattices-pbh-via-kgraphs, product-of-trees-faithful-factor-pbh-via-bass-serre-induction, boone-higman-type-a-class-closed-under-finite-extensions, type-a-action-gives-boone-higman-for-subgroups]
---

Notation as in `tree-lattice-kgraph-power-phase-proof`. Pass to the
factor-preserving `Γ_0` (finite index; `B_A` passes to finite-index overgroups).
Only the changes from the torsion-free argument are written out.

**Step T1 (transported k-graph C).** Choose a representative oriented cube `c_v`
in each `Γ_0`-orbit `v`, and for every oriented cube `w` an element `h_w ∈ Γ_0`
with `h_w c_[w] = w`. The paths of `C` from `v` are the finite grids starting at
`c_v`. Compose a grid `λ` ending at the cube `e(λ)` with a grid `μ` from
`c_[e(λ)]` by gluing `h_(e(λ)) μ` onto `λ`. Unique factorization of grids makes
`C` a finite `k`-graph, and `∂C(v) = B_(c_v)`. No freeness is needed.

**Step T2 (germ groupoid).** Let `G(v, v)` be the image of `Stab_(Γ_0)(c_v)` in
`Homeo(B_(c_v))`. These are finite groups, and `G` has objects `C^0` and no
morphisms between different objects. For `g ∈ G(v,v)`, with a lift `ĝ`, put
`g · λ = ĝ λ` (a grid from `c_v`) and
`φ(g, λ) = [h_(ĝ e(λ))^(-1) ĝ h_(e(λ))]`, the germ class in `G(s(λ), s(λ))`. An
element acting trivially on `B_(c_v)` fixes every grid from `c_v`, and its sections
act trivially on the sub-boxes. So these maps do not depend on the lift. The
identity `ĝ(λ ∪ h_(e(λ)) μ) = ĝλ ∪ h_(ĝe(λ)) (h_(ĝe(λ))^(-1) ĝ h_(e(λ))) μ` gives
`g·(λμ) = (g·λ)(φ(g,λ)·μ)`, and the other axioms of Li's self-similar actions
(TeX l.2183–2199) follow the same way. The action preserves degrees. Let
`D = C ⋈ G`.

**Step T3 (Li's condition (F) for D).** By Li's definition (TeX l.810–816), `[a, U]`
is the compact open bisection `a` of `I_l(D) ⋉ ∂Ω` restricted to `U`. For
`X = ∂Ω` the relevant sets `U` are the vertex boundaries `∂Ω(v)`. If
`a, b ∈ D^*(v,v) = G(v,v)` give the same bisection on `∂Ω(v)`, they induce the same
homeomorphism of `B_(c_v)`, so `a = b` in `G(v,v)`. The same computation shows that
an element of `I_l(D)` acting trivially on an open set has trivial germs there, so
the groupoid is effective and its full group consists of homeomorphisms.

**Step T4 (loops and strong connectivity).** For `α` an oriented `(k-1)`-cube in the
other factors, `H_α = Stab(α)` acts on `T_j` with finite stabilizers and finitely
many orbits (Lemma P). It is virtually free, so it has a finite-index free subgroup
`H'_α` acting freely. Closed colour-`j` walks of `C` at `v` of length `n` are
non-backtracking walks of length `n` from `e_j` that end in `H_α e_j`. They include
the lifts of closed walks at `[e_j]` in the Hashimoto graph of `H'_α \ T_j`, which
is irreducible with spectral radius greater than 1. So a sufficiently large common multiple `N` of the
periods (bh-refute nit N1) gives at least two loops of every colour at every vertex of `C_N`. Strong
connectivity of `C` follows as in Step 3 of the phase route, because the quotient
map from that Hashimoto graph to the colour-`j` classes is onto. `C_N` then splits
into strongly connected pieces as in Step 1 of
`virtually-torsion-free-tree-lattices-pbh-via-kgraphs`. `G` acts on each `C_N`
piece, since it preserves degrees and vertices.

**Step T5 (embedding).** Take phases and radius sets `C_r` as in Step 5 of the
phase route. For `γ ∈ Γ_0` and `ξ` in the box of `c ∈ C_r`, follow the grid of `ξ`
from `c` to a cube `w` on the common tail. Then `γ` acts near `ξ` as
`μ x ↦ μ' (g · x)`, with `g = [h_(γw)^(-1) γ h_w] ∈ G` and `μ, μ'` the transported
prefixes, chosen with degrees in `N·N^k` by the phase coordinate. So `γ` is a
global bisection of `I_l(D_N) ⋉ ∂Ω` on the phase space, and after removing
repetitions with two loops (Step 5 of the phase route) it lies in the full group
on `Z = ∂Ω`. The action is faithful, because `Γ_0` is faithful on `∏ ∂T_i`.

**Step T6 (finiteness and type (A)).** `C_N x O_2`, with `G` acting on the first
factor, satisfies the hypotheses of Li's Example `ex:ZS` (III) (TeX l.2371–2380):
- `C_N x O_2` is a finite higher rank graph with two loops of every colour at every
  vertex;
- the action preserves degrees, so Example `ex:ZS` makes the Zappa--Sz\'ep product
  right cancellative up to `=*` and supplies (Inv);
- condition (F) holds by Step T3;
- the unit groups `D^*(w,w) = G(w,w)` are finite, hence of type `F_∞` (Remark
  `rem:ZS-Stab`).
So the full group `D''` on `Z x {0,1}^N` is of type `F_∞`. Units of `G` do not change
cylinders, so Steps 2–4 of `stabilized-kgraph-full-group-clopen-action-proof`
(pieces, refinement comparison, type (A) on clopen sets) apply word for word. Hence
`D'' ∈ B_A`. `Γ_0 ≤ D''` via `g ↦ g x id`, so `Γ_0` and `Γ` lie in `B_A`.
