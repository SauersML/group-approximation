---
rg: 2
id: periodic-linf-proximity-complexes-are-contractible-proof
kind: route
title: Collapse boxes layer by layer by pushing boundary vertices one lattice step inward
target: periodic-linf-proximity-complexes-are-contractible
requires: []
---

**Dominated vertices.** In a flag complex `K`, call a vertex `u` dominated by a
different vertex `w` if `w` is adjacent to `u` and every neighbour of `u` is equal
or adjacent to `w`. Then the link of `u` is the flag complex of the neighbours of
`u`, which is a cone with apex `w`, so it is contractible. Since
`K = (K − u) ∪ st(u)` with `(K − u) ∩ st(u) = lk(u)`, and both `st(u)` and `lk(u)`
are contractible, the inclusion `K − u → K` of the full subcomplex on the other
vertices is a homotopy equivalence.

**Boxes.** Put `B_T = {x : ‖x‖_∞ <= T}` and let `K_T` be the full subcomplex of
`K_c(O)` on `O ∩ B_T`, which is finite. `O` meets `[0,1)^n ⊆ B_2`, so `K_2` is
nonempty. Any two points of `B_2` are within `4 <= c`, so `K_2` is a simplex.

**Layer removal.** Let `T >= 3` be an integer and let `u ∈ O ∩ (B_T ∖ B_(T−1))`.
Let `I = {i : |u_i| > T − 1}`, which is nonempty, and set
`w = u − Σ_(i∈I) sign(u_i) e_i`. Then:

- `w ∈ O`, since `O` is `Λ`-invariant;
- `w ∈ B_(T−1)`: for `i ∈ I`, `|w_i| = |u_i| − 1 <= T − 1` (no sign change since
  `|u_i| > 2`); for `i ∉ I`, `w_i = u_i` and `|u_i| <= T − 1`;
- `‖w − u‖_∞ = 1 <= c`, so `w` is adjacent to `u`;
- `w` dominates `u` inside any full subcomplex `L` with
  `O ∩ B_(T−1) ⊆ L^0 ⊆ O ∩ B_T`. Let `z` be a neighbour of `u` in `L`, so
  `z ∈ B_T` and `‖z − u‖_∞ <= c`. For `i ∉ I`, `|z_i − w_i| = |z_i − u_i| <= c`.
  For `i ∈ I` with `u_i > 0`: `z_i ∈ [u_i − c, T]` and `w_i = u_i − 1`, so
  `z_i − w_i ∈ [1 − c, T − u_i + 1] ⊆ [1 − c, 2)` because `T − u_i < 1`. Hence
  `|z_i − w_i| <= max(c − 1, 2) <= c`. The case `u_i < 0` is symmetric.

Remove the vertices of `O ∩ (B_T ∖ B_(T−1))` one at a time, in any order. At each
step the current complex is such an `L`, and the dominating vertex `w` lies in
`B_(T−1)`, so it is never removed during this stage. Each removal is a homotopy
equivalence, so `K_(T−1) → K_T` is a homotopy equivalence. By induction every
`K_T` with integer `T >= 2` is homotopy equivalent to the simplex `K_2`, hence
contractible.

**Whole complex.** Every finite subcomplex of `K_c(O)` lies in some `K_T`. A map
from a sphere has compact image, which lies in a finite subcomplex (weak
topology), so it is null-homotopic inside a contractible `K_T`. Hence all
homotopy groups of `K_c(O)` vanish, and `K_c(O)` is contractible by Whitehead's
theorem.
