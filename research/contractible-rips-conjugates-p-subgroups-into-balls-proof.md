---
rg: 2
id: contractible-rips-conjugates-p-subgroups-into-balls-proof
kind: route
title: Free simplicial chains bound torsion-free subgroups, and a Smith fixed point is a simplex whose vertices conjugate P into the d-ball
target: contractible-rips-conjugates-p-subgroups-into-balls
requires:
  - smith-fixed-point-theorem-for-finite-p-groups
---

Notation: `R = R_d(G,S)`. `G` acts on `R` by left multiplication, which preserves
`d_S`, so it acts simplicially. `N = |B_S(d)|`.

**Step 0 (local finiteness and dimension).** If `σ` is a simplex and `x ∈ σ`, then
`σ ⊆ x B_S(d)`, so `|σ| <= N`. Hence `dim R <= N - 1`, and every vertex lies in
finitely many simplices.

**Step 1 (stabilizers).** Let `G_σ = {g : gσ = σ}` be the setwise stabilizer of a
simplex `σ`, and fix `x ∈ σ`. If `g ∈ G_σ` then `gx ∈ σ`, so `g ∈ σ x^-1`. Hence
`|G_σ| <= |σ|` and `G_σ` is finite.

**Step 2 (dimension bound).** Let `H <= G` be torsion-free, and let `R'` be the
barycentric subdivision of `R`. The vertices of `R'` are the simplices of `R`, and
a simplex of `R'` is a chain `σ_0 ⊊ ... ⊊ σ_k`.

- If `h ∈ H` fixes a simplex of `R'` setwise, it preserves the chain. The `σ_i` have
  distinct sizes, so it fixes each of them, and `h ∈ G_{σ_0}`.
- That group is finite by Step 1, so `h` has finite order, and `h = 1`.

So `H` permutes the simplices of each dimension of `R'` freely. The simplicial
chain groups `C_k(R')` are therefore free `ZH`-modules. Orientations are
preserved because the action on vertices of a simplex is trivial.

`R'` is contractible, so the augmented complex
`0 → C_(N-1)(R') → ... → C_0(R') → Z → 0` is exact. It is a free resolution of the
trivial module `Z` of length at most `N - 1`, and so `cd H <= N - 1` (Brown,
*Cohomology of Groups*, VIII.2, the definition of cd by projective resolutions).

**Step 3 (Smith invariant).** Let `P <= G` be a finite `p`-group. `|R|` is a
locally finite simplicial complex of dimension `<= N - 1` and it is contractible,
so it is finitistic with the mod `p` homology of a point. By
`smith-fixed-point-theorem-for-finite-p-groups` there is a point `z ∈ |R|` fixed by
`P`.

Let `σ` be the unique simplex of `R` whose open simplex contains `z`. Every `g ∈ G`
maps open simplices onto open simplices, and `P` fixes `z`, so `Pσ = σ`. Pick
`y ∈ σ`. For `q ∈ P` we have `qy ∈ σ`, so `d_S(qy, y) <= d`, that is
`|y^-1 q y|_S <= d`. Therefore `y^-1 P y ⊆ B_S(d)`.

**Step 4 (counting).** Conjugation preserves order, so `|P| <= N`. Each finite
subgroup of prime-power order is conjugate to a subgroup contained in the finite
set `B_S(d)`. There are at most `2^N` subsets of `B_S(d)`, so there are at most
`2^N` conjugacy classes of such subgroups.
