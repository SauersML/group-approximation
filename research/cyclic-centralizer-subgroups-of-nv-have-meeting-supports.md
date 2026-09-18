---
rg: 2
id: cyclic-centralizer-subgroups-of-nv-have-meeting-supports
kind: claim
title: In a Brin–Thompson group nV, supports are clopen, and in any torsion-free subgroup with cyclic centralizers (e.g. a closed hyperbolic surface group) every two nontrivial supports meet, as do every support and each of its translates
distinct_from:
  closed-hyperbolic-surface-groups-embed-in-thompson-v: that is the open survey Question 4.7; this is a structural constraint any such embedding (into V or any nV) must satisfy, and it does not decide the question.
  subshift-elementary-group-rigid-supports-are-mutual-centralizers: that concerns rigid stabilizers in subshift elementary groups; this concerns supports of individual elements of nV and uses only centralizer structure of the subgroup.
---

**ESTABLISHED** (lane proof below, elementary, not reviewed; no priority claimed).

Let `C` be the Cantor set and `nV ≤ Homeo(C^n)` the Brin–Thompson group. For `g ∈ nV` put
`W(g) = int Fix(g)` and `supp(g) = C^n \ W(g)`.

1. **Supports are clopen.** For every `g ∈ nV`, `W(g)` is a finite union of bricks, so `supp(g)` is
   clopen. Also `supp(g^m) ⊆ supp(g)` for every `m`.
2. **Meeting supports.** Let `Γ ≤ nV` be torsion-free, with the centralizer of every nontrivial element
   cyclic. This holds for every torsion-free hyperbolic group, in particular every closed hyperbolic surface
   group. Then for all nontrivial `g, h ∈ Γ`:
   - `supp(g) ∩ supp(h) ≠ ∅`;
   - `γ·supp(g) ∩ supp(g) ≠ ∅` for every `γ ∈ Γ`. In particular, no `γ ∈ Γ` maps `supp(g)` into `W(g)`.

## Proof

1. Write `g` on a brick partition `{B_j}`, with `g(u^{(j)}x) = v^{(j)}x` coordinatewise on `B_j`. If
   `u^{(j)} = v^{(j)}`, then `g` is the identity on `B_j`. Otherwise some coordinate `i` has
   `u_i ≠ v_i`, and `u_i x_i = v_i x_i` has at most one solution:
   - it has none unless one of `u_i, v_i` extends the other, say `v_i = u_i w`;
   - in that case `x_i = w x_i` forces `x_i = w^∞`.

   So `Fix(g) ∩ B_j` lies in a set whose `i`-th coordinate is a single point, and is nowhere dense in
   `B_j`. Hence `W(g)` is exactly the union of the identity bricks, which is clopen. Where `g` is the
   identity on an open set, so is `g^m`, so `supp(g^m) ⊆ supp(g)`.
2. Suppose `supp(g) ∩ supp(h) = ∅`.
   - Then `g` and `h` commute: each acts as the identity on the other's support, and both preserve their
     own supports.
   - So `h` lies in the centralizer of `g`, which is cyclic, and `g^m = h^k` for some `m, k ≠ 0`. Both
     are nontrivial because `Γ` is torsion-free and infinite cyclic groups have no torsion.
   - By item 1, `supp(g^m) ⊆ supp(g)` and `supp(h^k) ⊆ supp(h)`, which are disjoint. So the element
     `g^m = h^k` has empty support, i.e. `g^m = 1`, a contradiction.

   For the second bullet, apply this to `h = γgγ^{-1}`, whose support is `γ·supp(g)`. It is
   nontrivial, and it is a power of `g` only if `supp(g) = γ·supp(g)`, so the argument above applies
   verbatim whenever the two supports are disjoint. ∎

## Scope and reading

- This does **not** decide Question 4.7. The statement holds in `2V`, where every closed hyperbolic surface
  group embeds (see `closed-hyperbolic-surface-groups-embed-in-thompson-v`). So any obstruction to `V` must use
  one-dimensional dynamics, as Bleak–Salazar-Díaz's `Z^2 * Z` argument does.
- **Constraint on constructions.** An embedding of `π_1(Σ_g)` into `V` or `nV` can never contain two nontrivial
  elements supported on disjoint clopen sets. So disjoint-support "ping-pong" building blocks, like the RAAG
  lamp constructions, cannot be used directly. Every nontrivial element's support must meet all of its
  translates.
- **Consequence for identity regions.** If some nontrivial `g ∈ Γ` has `W(g) ≠ ∅`, then no element of `Γ` has
  an attracting set inside `W(g)` whose basin contains `supp(g)`. That is a necessary condition on the
  north–south dynamics of the embedded surface group.
