---
rg: 2
id: two-leaf-graph-manifold-twist-realizations
kind: claim
title: For a graph manifold with two leaf blocks, fibering means parallel boundary words in the JSJ torus; in a mapping class group realization whose JSJ torus goes to a two-curve twist group, each fiber is a single twist power, point pushing on both sides gives only fibered manifolds, and a non-virtually-fibered example needs one block with a new boundary slope ratio
distinct_from:
  fiber-detecting-block-characters-force-npc-graph-manifolds: that excludes local product hosts for every graph manifold that is not non-positively curved, through charges; this analyses mapping class group realizations of the simplest charged configuration, two leaf blocks glued along one torus, where local products are not assumed.
  nonfibered-graph-manifold-groups-have-no-fg-normal-subgroups: that constrains intersections with normal free or surface subgroups of hosts; this constrains how fibers and boundary words map into twist groups.
  virtually-fibered-3-manifold-groups-satisfy-pbh: that realizes fibered groups through the Birman sequence; item 4 here identifies that construction inside the two-leaf picture and shows it cannot leave the fibered case.
---

**ESTABLISHED** for items 1, 3 and 4 (lane proof, elementary; not independently reviewed).
Item 2 is a reading of Svetlov's Theorem III (arXiv:math/0112308v2, as quoted in
`fiber-detecting-block-characters-force-npc-graph-manifolds`) for a two-vertex graph, and
should be checked by a referee. Item 5 states an open design problem.

## Setting

`G = G_v *_E G_w` with `G_v = F_v x <t_v>`, `F_v = pi_1(Σ_{h,1})` free of rank `2h >= 2` and
boundary word `c_v = Π [a_i, b_i]`, and likewise for `w` (genus `h'`). `E = <c_v, t_v> =
<c_w, t_w> ≅ Z^2`, with `t_v, t_w` not rationally parallel. This is `pi_1` of a closed graph
manifold with one JSJ torus and two leaf blocks `Σ_{h,1} x S^1`, `Σ_{h',1} x S^1`. In
`E ⊗ Q` write `t_w = β_v t_v + γ_v c_v` and `t_v = β_w t_w + γ_w c_w`.

## Statement

1. **Fibering.** `G` has a homomorphism to `Z` that is nonzero on both fibers iff `c_v` and
   `c_w` are rationally parallel in `E`, iff `β_v β_w = 1`.
2. **Virtual fibering (reading of Svetlov).** The charges satisfy `k_v k_w b^2 = β_v β_w`,
   where `b` is the fiber intersection number. The matrix `H_M` is then `diag(|k_v|, |k_w|)`
   when `k_v k_w <= 0`, and `[[|k_v|, -1/|b|], [-1/|b|, |k_w|]]` when
   `k_v k_w > 0`. So `M` is virtually fibered iff `0 < β_v β_w <= 1` or `β_v = β_w = 0`. In
   particular it is not virtually fibered when `β_v β_w <= 0` (not both zero) or
   `β_v β_w > 1`.
3. **Two-curve twist realizations.** Let `ρ : G -> Mod^+(S)` be injective, `S` of finite
   type, with `ρ(E) <= <T_x, T_y>` for disjoint, essential, non-peripheral, non-isotopic
   curves `x, y`. Then, after swapping `x` and `y`, `ρ(t_v) = T_y^k`, `ρ(t_w) = T_x^{k'}`,
   `ρ(c_v) = T_x^m T_y^n` and `ρ(c_w) = T_x^{m'} T_y^{n'}`, with `k, k', m, n' != 0`. Also
   `ρ(F_v)` fixes `y`, `ρ(F_w)` fixes `x`, and `β_v β_w = n m' / (m n')`.
4. **Point pushing.** If both blocks are realized by Birman point pushing (`ρ(F_w)` the
   pushes of a puncture `p` around loops of a subsurface `Y` with `∂Y ⊇ x`, where `y` is
   the curve parallel to `x` across `p`, and similarly for `v`), then `ρ(c_v)` and
   `ρ(c_w)` are both `±T_x T_y^-1`. So `c_v ∥ c_w`, and by item 1 `G` maps to `Z` nonzero on both fibers. This is the Birman
   embedding of a surface-by-cyclic group, seen in this picture.
5. **The design problem (open).** Keep `v` pushed, so `n/m = -1`. By items 2--3, a
   realization of a non-virtually-fibered `G` in this shape needs a leaf block `w` with
   `ρ(F_w) <= Stab^+(x)` free of rank `2h'` and relator product
   `Π [ρ(a'_i), ρ(b'_i)] = T_x^{m'} T_y^{n'}` whose **boundary slope ratio** `m'/n'` lies
   outside `[-1, 0)`, since `β_v β_w = -m'/n'`. Pushing gives exactly `m'/n' = -1`.
   - Since `T_x` is central in `Stab^+(x)`, `m'` is determined by `n'` and the induced map
     of `F_w` to `Stab^+(x)/<T_x>`, independently of the lifts. So the ratio is an
     Euler-number-type invariant of that map.
   - Orientation reversal does not change it.
   - An example also needs injectivity of `G_v *_E G_w -> Mod(S)`. With a puncture or
     boundary on `S` it would then lie in `B_A` (`punctured-surface-mcgs-satisfy-permutational-boone-higman`).
     Neither the free subgroup nor the injectivity is constructed here.

## Proof

**Item 1.** A homomorphism `φ : G -> Q` has `φ(c_v) = φ(c_w) = 0`, since both are products
of commutators. If `c_v, c_w` are independent in `E ⊗ Q`, then `φ|_E = 0`, so `φ(t_v) = 0`.
If they are parallel, define `φ` on `G_v` by `a_i, b_i -> 0` and `t_v -> 1`. Its restriction to
`E` is the functional that kills `c_v` and sends `t_v` to `1` (integral, since `(c_v, t_v)` is a
basis of `E`); it kills `c_w`, so it extends to `G_w` by `a'_i, b'_i -> 0` and
`t_w -> φ(t_w)`. Here `φ(t_w) != 0`, since otherwise `t_w ∥ c_v ∥ c_w`, but `(c_w, t_w)` is a
basis of `E`. For the equivalence with `β_v β_w = 1`: substituting the first expansion into
the second gives `γ_w c_w = (1 - β_v β_w) t_v - β_w γ_v c_v`, and `γ_w != 0` since `t_v, t_w` are
not parallel. As `(c_v, t_v)` is a basis, `c_w ∥ c_v` iff `β_v β_w = 1`.

**Item 2.** Each block is a leaf, so `ι_*(c_v) = 0` in `H_1(M_v; Q)` and
`ι_*(f_{-w}) = β_v f_v`; Svetlov's charge is `k_v = β_v / b_w` (item 1 of the proof of
`fiber-detecting-block-characters-force-npc-graph-manifolds`), and likewise `k_w = β_w / b_w`.
The two forms of `H_M` follow from its definition (l.523--545): if `k_v k_w <= 0` the
vertices are not equivalent and the graph of signed components is the single edge,
bipartite with `s = sgn k`; if `k_v k_w > 0` they are equivalent, the edge is absorbed, and
`s(v) = s(w)`. Theorem III (VF): semipositive and supersingular, or a negative eigenvalue.
A diagonal `diag(|k_v|, |k_w|)` with a nonzero entry has neither. The `2 x 2` matrix in the
second case has a negative eigenvalue iff `k_v k_w < 1/b^2`, and is semipositive with a
nowhere-zero kernel vector iff `k_v k_w = 1/b^2`.

**Item 3.** Write `ρ(t_v) = T_x^p T_y^q`. Every element of `ρ(G_v)` commutes with it, so it
permutes `{x, y}` preserving weights, since a multitwist determines its weighted multicurve
(Farb--Margalit, *Primer*, §3.3). An index at most two subgroup `F^0` of `ρ(F_v)` fixes `x`
and `y`. If `p, q != 0`, then `ρ(c_v) ∈ <T_x, T_y>` lies in `F^0` and commutes with it. But
`F^0` is free of rank at least two, with trivial center, and `ρ(c_v) != 1`: contradiction.
So `ρ(t_v)` is a power of one twist, say `T_y^k`; then `ρ(F_v)` fixes `y`. If `m = 0`,
`ρ(c_v) = T_y^n` commutes with `ρ(F_v)`: the same contradiction. The same argument applies
to `w`. Its fiber cannot be a power of `T_y`, or `t_v ∥ t_w`; so it is `T_x^{k'}` and
`n' != 0`. The formula for `β_v β_w` is linear algebra in `<T_x, T_y> ≅ Z^2`:
`β_v = -n k'/(m k)` and `β_w = -m' k/(n' k')`.

**Item 4.** `Push(ℓ) = T_{ℓ_1} T_{ℓ_2}^-1` for a simple loop `ℓ` through the puncture, where
`ℓ_1, ℓ_2` bound its annular neighborhood (Farb--Margalit, *Primer*, Fact 4.7). For the
boundary-parallel loop these are `x` and `y`. So `ρ(c_w) = (T_x T_y^-1)^{±1}`, and likewise
for `v` with the roles of the two curves exchanged.

## Scope

- Only two leaf blocks and only edge images in a two-curve twist group are treated. Edge
  images with pseudo-Anosov components, three or more curves (e.g. disk pushing), or more
  blocks are not.
- Item 2 relies on reading Svetlov's graph of signed components correctly; items 1, 3 and 4
  do not. In item 5, the non-fibered range `m'/n' != -1` needs only item 1; the
  non-virtually-fibered range `m'/n' ∉ [-1, 0)` uses item 2.
