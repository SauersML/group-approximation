---
rg: 2
id: stw99-l-row-unitaries-detect-edge-phase-proof
kind: route
title: Multiply the row out against the Cuntz-Krieger relations
target: stw99-l-row-unitaries-detect-edge-phase-actions
requires:
  - stw99-l-pi1-aut-splits-into-two-hom-groups
---

**Direct computation.**  Conventions: `s_a^* s_b = delta_{ab} p_{r(a)}`,
`sum_{s(a)=i} s_a s_a^* = p_i`, `sum_i p_i = 1`.

*`R_i R_i^* = 1`.*  The edge entries of `R_i` are exactly the edges with
source `i`, namely the `a_{ij}^{(k)}` for `k <= u_j` together with `d_i`
in column `(i, u_i+1)`, so their range projections are orthogonal and sum
to `p_i`.  The remaining columns contribute `p_j` once for each `j != i`.

*`R_i^* R_i = P`.*  The diagonal entry in column `(j,k)` is `p_{r(a)}=p_j`
for an edge entry, `p_i` for `(i,u_i+1)`, and `p_j` for a projection
entry -- always `p_j`, independently of `i`.  Off-diagonal entries vanish:
distinct edges by the edge relation, distinct projections by vertex
orthogonality, and a mixed pair because `s_a = p_{s(a)} s_a` with
`s(a) = i != j`.

*Unitarity.*  `W_i W_i^* = R_i (R_n^* R_n) R_i^* = R_i P R_i^*
= R_i R_i^* R_i R_i^* = 1`, and symmetrically `W_i^* W_i = 1`.

*The circle action.*  `|z| = 1` makes the rescaling preserve both
Cuntz--Krieger relations, and `g_{ij,z}^{-1} = g_{ij,zbar}`; continuity
is inherited from the canonical `T^{E^1}` action, of which this is a
coordinate.

*Equation (4).*  `i < n` means the rescaled edge has source `i != n`, so
`g` fixes `R_n`, whence `g(W_k) W_k^* = g(R_k) P R_k^* = g(R_k) R_k^*`.
For `k != i` that is `R_k R_k^* = 1`.  For `k = i` the row differs in the
single column `(j,1)`, so the sum `R_i R_i^* = 1` is corrected by
`-s_a s_a^* + z s_a s_a^*`.

*Equation (5).*  By the Bott convention imported from the target's
prerequisite, the class of `1 + (z-1)p` is `[p]`, and
`s_a s_a^* ~ s_a^* s_a = p_{r(a)} = p_j`.  The `K_0` component vanishes
because every vertex projection is fixed for all `z`.
