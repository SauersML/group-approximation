---
rg: 2
id: fg-subgroups-of-nv-finite-iff-germ-finite-proof
kind: route
title: "Brick induction over words: bounded offsets at one point make every element act brick-wise near it; compactness then bounds the whole group"
target: finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite
requires: []
---

The notation is as in the target. `|·|` is the sup norm on `Z^n`. For `m ∈ Z`,
"level `≥ m`" means every coordinate of the level is `≥ m`.

**Step 0 (depth).**
- Let `g ∈ nV` have a table whose domain words have length `≤ L`.
- Let `B = Π C(a_j)` be a brick of level `≥ L`. For every table brick
  `Π C(u_j)`, each `C(a_j)` is either inside `C(u_j)` or disjoint from it, since
  `|a_j| ≥ |u_j|`. So `B` lies inside one table brick.
- Hence `g|_B` is a prefix replacement onto a brick of level
  `level(B) + c(g)|_B`, and `c(g)` is constant on `B`. Call the least such `L`
  the *depth* of `g`.
- A prefix replacement from `Π C(a_j)` onto `Π C(b_j)` is the unique map
  `(a_j w_j) ↦ (b_j w_j)`. So `g|_B` is determined by the brick `gB`.
- Composites of prefix replacements between bricks are prefix replacements.

**Step 1 (brick induction).**
- Let `S` be a finite symmetric generating set of `K`, and let `L` be the
  maximum depth of the elements of `S`.
- Fix `x` and suppose `|c(g)(x)| ≤ M_x` for all `g ∈ K`. Let `B_x` be the brick
  of level exactly `L + M_x` containing `x`.
- **Claim.** For every word `s_r ⋯ s_1` in `S`, the element `h = s_r ⋯ s_1` acts
  on `B_x` as a prefix replacement with constant offset `c(h)(x)`.
- **Proof, by induction on `r`.** The case `r = 0` is clear. Suppose the claim
  holds for `h' = s_{r-1} ⋯ s_1`.
  - `h'(B_x)` is a brick of level `L + M_x + c(h')(x) ≥ L`, because
    `|c(h')(x)| ≤ M_x`.
  - By Step 0, `s_r` acts on `h'(B_x)` as a prefix replacement with constant
    offset.
  - Composing, `h` acts on `B_x` as a prefix replacement. Its offset is constant
    on `B_x`, and by the cocycle rule it equals `c(h)(x)`.
- **Consequences.**
  - `|c(g)(y)| ≤ M_x` for all `g ∈ K` and all `y ∈ B_x`.
  - Every `g ∈ K` restricted to `B_x` is determined by `gB_x`. That brick has
    level in `[L, L + 2M_x]^n` in each coordinate, and there are finitely many
    such bricks. So `K` has finitely many germs at `x`, and the orbit `Kx` is
    finite.

**Step 2 (3 ⇒ 2).**
- By Step 1, every `x` has an open neighbourhood `B_x` on which offsets are
  bounded by `M_x`.
- By compactness, finitely many `B_{x_1}, …, B_{x_k}` cover `C^n`.
- So `M = max_i M_{x_i}` bounds all offsets.

**Step 3 (2 ⇒ 1).**
- Run Step 1 with the uniform bound `M` and every brick `B` of level exactly
  `L + M`. There are `2^{n(L+M)}` such bricks, and they partition `C^n`.
- Every `g ∈ K` acts on each `B` as the prefix replacement onto `gB`, a brick
  with level in `[L, L+2M]^n`.
- Let `N` be the number of bricks with level in `[L, L+2M]^n`. The map
  `g ↦ (gB)_B` is injective, so `|K| ≤ N^{2^{n(L+M)}}`.

**Step 4 (1 ⇒ 5).**
- Orbits of a finite group are finite.
- Let `h ∈ Stab_K(x)` have order `r`. At a fixed point the cocycle rule gives
  `c(h^k)(x) = k·c(h)(x)`, so `r·c(h)(x) = c(id)(x) = 0` and `c(h)(x) = 0`.
- **Zero offset gives local identity.** Take the brick `Π C(u_j) ∋ x` on which
  `h` is the prefix replacement onto `Π C(v_j)`, with `|v_j| = |u_j|`.
  - Write `x = (u_j w_j)_j`. Then `hx = (v_j w_j)_j = x`, so `v_j` is the
    length-`|u_j|` prefix of `x_j`, which is `u_j`.
  - So `h` is the identity on that brick. This is Step 2 of
    `brin-thompson-exponent-cocycle-proof`.

**Step 5 (5 ⇒ 4 ⇒ 3).**
- If `gx = g'x`, then `g^{-1}g' ∈ Stab_K(x)` is the identity near `x`. So `g`
  and `g'` have the same germ at `x`.
- Hence the germs at `x` are indexed by the finite orbit `Kx`.
- Offsets at `x` are read off from germs, so they take finitely many values.

**Step 6 (6).**
- **6 ⇒ 2.** `|c(g)(x)| ≤ 2 sup|ξ|`.
- **1 ⇒ 6.** Put `ξ_j(x) = max_{g ∈ K} c_j(g)(x)`. This is a finite maximum of
  locally constant functions, hence continuous. Moreover
  `ξ_j(hx) = max_g c_j(g)(hx) = max_g (c_j(gh)(x) - c_j(h)(x)) = ξ_j(x) - c_j(h)(x)`,
  because `g ↦ gh` is a bijection of `K`.

**Step 7 (addendum).**
- Suppose every orbit is finite and every finite-index subgroup of `K` has finite
  abelianization.
- For each `x`, `H = Stab_K(x)` has finite index. `χ_x(h) = c(h)(x)` is a
  homomorphism `H → Z^n`, by the cocycle rule at the fixed point `x`.
- The image of `χ_x` is a finite subgroup of `Z^n`, so `χ_x = 0`.
- By Step 4, each `h ∈ H` is the identity near `x`. So condition 5 holds, and
  `K` is finite.
- Conversely, finite groups have finite orbits.

**Step 8 (corollaries).**
- **Kazhdan.** Let `K` be a Kazhdan group and let `ℓ^2(Kx)` have almost
  invariant vectors. Then it has a nonzero invariant vector, which is constant
  on the transitive set `Kx` and square-summable, so `Kx` is finite. Apply the
  addendum.
- **Torsion.** Step 4 shows stabilizer elements of finite order are the identity
  near their fixed point. So condition 5 reduces to finite orbits.
- **Full shift.** Let `K` lie in the topological full group of the full shift
  inside `2V`. Its orbits lie in shift orbits, which are copies of `Z`, and the
  generators move points by at most `r` steps.
  - An infinite orbit is then an infinite subset of `Z`, and generators move
    along it by at most `r`.
  - Intervals `[-R, R]` meet the orbit in Følner sets. A generator changes each
    such set only within `r` of its endpoints, while the set itself grows
    without bound.
  - So an infinite orbit carries almost invariant vectors, and a Kazhdan `K`
    would have to have finite orbits.
