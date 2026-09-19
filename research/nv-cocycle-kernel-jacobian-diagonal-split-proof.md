---
rg: 2
id: nv-cocycle-kernel-jacobian-diagonal-split-proof
kind: route
title: "Rank-one functionals of the exponent cocycle cut out subgroups; the positive-diagonal one is a block-interleaved Higman-Thompson group, the Jacobian one is the measure-preserving subgroup, and cosets of two subgroups meet in cosets of the intersection"
target: nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal
requires:
  - brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination
  - haagerup-splits-as-coset-plus-subgroup-properness
  - full-shift-topological-full-group-embeds-in-2v
  - brin-thompson-nv-fibre-elements-are-cubically-elliptic
  - nv-gap-class-cocycles-are-coboundaries
---

Notation as in the target. Throughout, `g ∈ nV` is a prefix replacement
`[u_1]×…×[u_n] → [u'_1]×…×[u'_n]` on each brick of a finite brick partition, and
`c(g)(x) = (|u'_i| − |u_i|)_i` on that brick. Well-definedness of `c` and the cocycle identity
`c(gh) = c(g)∘h + c(h)` are imported from `brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`
(Setting). Taking `h = g^{-1}` gives `c(g^{-1}) = −c(g)∘g^{-1}`.

## Item 1 (subgroups and intersections)

Let `ℓ: Z^n → Z` be a homomorphism. If `ℓ∘c(g) ≡ 0` and `ℓ∘c(h) ≡ 0`, then
`ℓ∘c(gh) = ℓ∘c(g)∘h + ℓ∘c(h) ≡ 0` and `ℓ∘c(g^{-1}) = −ℓ∘c(g)∘g^{-1} ≡ 0`. So `H_ℓ` is a subgroup.
The same computation works for `D_v`, because `Zv` is a subgroup of `Z^n`: if `c(g)` and `c(h)`
take values in `Zv` pointwise, so do `c(g)∘h + c(h)` and `−c(g)∘g^{-1}`. Every element of `K` has
`c ≡ 0 ∈ Zv` and `ℓ(0) = 0`, so `K ≤ H_ℓ` and `K ≤ D_v`.

If `ℓ_1, …, ℓ_n` are linearly independent, the map `t ↦ (ℓ_1(t), …, ℓ_n(t))` is injective on
`Z^n`. So `ℓ_i(c(g)(x)) = 0` for all `i` forces `c(g)(x) = 0`, pointwise. Hence
`⋂_i H_{ℓ_i} = K`.

For `M_n ∩ D`: if `g ∈ D` then `c(g)(x) = k(x)(1,…,1)` with `k(x) ∈ Z`. If also `g ∈ M_n`, then
`0 = ℓ_+(c(g)(x)) = n·k(x)`, so `k(x) = 0` and `c(g)(x) = 0`. Hence `M_n ∩ D ⊆ K`, and the reverse
inclusion was shown above.

## Item 2 (positive directions are Higman–Thompson groups)

Let `v = (p_1, …, p_n)` with all `p_i ≥ 1`, `s = Σ p_i`, and `A = {0,1}^s`. Here `V_{2^s,1}` is the
group of homeomorphisms of `A^ω` that are prefix replacements `w y ↦ w' y` (`w, w' ∈ A^*`) on the
cylinders of some finite partition of `A^ω` into cylinders, with the image cylinders again a
partition.

**The coding.** For `x = (x_1, …, x_n) ∈ C^n`, cut each `x_i` into consecutive blocks of length
`p_i`, and let the `j`-th letter of `Z_v(x)` be the tuple of the `j`-th blocks,
`(x_1[jp_1, (j+1)p_1), …, x_n[jp_n, (j+1)p_n)) ∈ A`. This is a bijection that re-indexes
coordinates, so `Z_v` is a homeomorphism.

**Balanced bricks.** Call a brick `[u_1]×…×[u_n]` *balanced of level `L`* if `|u_i| = L p_i` for
all `i`. Then `Z_v` maps it onto the cylinder `[w]` of a unique word `w ∈ A^L`, and every cylinder
of `A^ω` arises this way. Because each `|u_i|` is a multiple of `p_i`, the blocks of `u_i y_i` are
the blocks of `u_i` followed by the blocks of `y_i`, so `Z_v(u_1 y_1, …, u_n y_n) = w·Z_v(y)`. Hence
the balanced-brick prefix replacement `(u_i y_i)_i ↦ (u'_i y_i)_i`, of levels `L → L'`, is
conjugated by `Z_v` to the word prefix replacement `w y ↦ w' y`, and conversely.

**`Z_v^{-1} V_{2^s,1} Z_v ⊆ D_v`.** Given `f ∈ V_{2^s,1}` with its cylinder partition, pull the
cylinders back to balanced bricks. On a brick of level `L` mapped to level `L'`, the conjugate
`Z_v^{-1} f Z_v` is a brick prefix replacement with `c = (L'p_i − Lp_i)_i = (L' − L)v`. So the
conjugate is in `nV` with values of `c` in `Zv`.

**`Z_v D_v Z_v^{-1} ⊆ V_{2^s,1}`.** Let `g ∈ D_v`. On a brick `B = [u_1]×…×[u_n]` of its table,
`g` maps onto `[u'_1]×…×[u'_n]`. Since `c(g)` is constant on `B` and lies in `Zv`, and `p_1 ≥ 1`,
there is an integer `k` with `|u'_i| − |u_i| = k p_i` for every `i`. Choose `L` with
`L p_i ≥ |u_i|` for all `i`. Subdivide `B` into the bricks `[u_1 w_1]×…×[u_n w_n]` with
`|w_i| = L p_i − |u_i|`. Each is balanced of level `L`. `g` maps it by prefix replacement onto
`[u'_1 w_1]×…×[u'_n w_n]`, and `|u'_i w_i| = |u'_i| − |u_i| + L p_i = (L + k)p_i`, so the image is
balanced of level `L + k`. Doing this on every brick of the table gives partitions of `C^n` into
balanced bricks, for the domain and for the image, such that `g` is a balanced prefix replacement
on each piece. By the previous paragraph `Z_v g Z_v^{-1}` is a word prefix replacement on each
cylinder of a finite cylinder partition, with image cylinders forming a partition. So it lies in
`V_{2^s,1}`.

Both inclusions give `Z_v D_v Z_v^{-1} = V_{2^s,1}`. For `v = (1, …, 1)` this is
`D ≅ V_{2^n,1}`, and `K ≤ D` by item 1.

## Item 3 (the Jacobian subgroup)

**(a)** Let `g` map the brick `B = [u_1]×…×[u_n]` onto `B' = [u'_1]×…×[u'_n]` by prefix replacement.
The replacement carries the normalized Haar measure of `B` to that of `B'`, and
`λ(B) = 2^{−Σ|u_i|}`, `λ(B') = 2^{−Σ|u'_i|}`. So `g_*(λ|_B) = 2^{J(g)|_B} · λ|_{B'}`, where
`J(g)|_B = Σ(|u'_i| − |u_i|)` is the constant value of `J(g)` on `B`. Summing over the table of `g`
gives `g_*λ = λ` iff `J(g) = 0` on every brick of the table, that is, iff `g ∈ M_n`. (If
`J(g)|_B ≠ 0`, then `g_*λ(B') = 2^{J(g)|_B} λ(B') ≠ λ(B')`, since the image bricks are disjoint.)

**Coordinates for `n = 2`.** `Φ(a, b)_i = a_i` for `i ≥ 0` and `Φ(a, b)_i = b_{−1−i}` for `i < 0`.
So `Φ([u]×[w])` is the cylinder of `X` that fixes the positions `[−|w|, |u|)`. Conversely, every
cylinder fixing a window `[−β, α)` with `α, β ≥ 0` is the image of a unique brick with side lengths
`(α, β)`. Recall `σ^k(x)_i = x_{i+k}`: the symbol at position `p` of `x` sits at position `p − k`
of `σ^k x`.

**One prefix replacement.** Let `g` map `[u]×[w]` onto `[u']×[w']`, and put
`k = |u| − |u'|` and `k' = |w'| − |w|`. For `x = Φ(uy, wz)`, the symbol `y_m` sits at position
`|u| + m` of `x` and at position `|u'| + m = (|u| + m) − k` of `Φ g Φ^{-1}(x)`. The symbol `z_m`
sits at position `−1 − |w| − m` of `x` and at position `−1 − |w'| − m = (−1 − |w| − m) − k'` of
the image. Now suppose `J(g) = 0` on this brick, i.e. `k = k'`. Then `Φ g Φ^{-1}(x)` agrees with
`σ^k(x)` outside the window `[−|w'|, |u'|)`, and inside that window it is the fixed pattern
`(w', u')`. Call such a map on a cylinder a *shift-and-overwrite* map.

**(b)** By the last paragraph, `Φ M_2 Φ^{-1}` consists of homeomorphisms of `X` that are
shift-and-overwrite on the cylinders of a finite partition. Conversely, let `f` be a homeomorphism
of `X` such that every point has a cylinder neighbourhood on which `f` is `σ^k` followed by
overwriting a finite window by a fixed pattern. By compactness finitely many such cylinders cover
`X`. The restriction of a shift-and-overwrite map to a subcylinder is again one, so we may refine
to a partition into cylinders `U` fixing `[−m, m)` for one large `m`. Enlarging `m` beyond `|k|`
and beyond the overwritten windows, on each `U` the map `f` is `σ^k` followed by overwriting
exactly the window `[−m − k, m − k)`, because `σ^k` already carries the fixed pattern of `U` there.
So `Φ^{-1} f Φ` is, on the brick of side lengths `(m, m)`, the prefix replacement onto a brick of
side lengths `(m − k, m + k)`. `f` is a bijection, so the image cylinders partition `X`. Hence
`Φ^{-1} f Φ ∈ 2V`, and its exponent cocycle there is `(−k, k)`, so `J = 0` and it lies in `M_2`.
The germs `x ↦ σ^k(x)` with finitely many coordinates changed are exactly the germs of the étale
groupoid generated by the shift and the homoclinic (finite-difference) relation. So `Φ M_2 Φ^{-1}`
is the topological full group of that groupoid.

**(c)** An element of `[[X]]` is locally `σ^k`. That is the shift-and-overwrite case in which the
overwrite on `U` rewrites the window `[−m − k, m − k)` with the pattern that `σ^k` already puts
there. So by (b) its conjugate lies in `M_2`, with cocycle `(−k(x), k(x))`. This agrees with the
embedding of `full-shift-topological-full-group-embeds-in-2v`, which is the same conjugation.
The baker's map `Φ^{-1} σ Φ` is the case `k ≡ 1`: `(a, b) ↦ (a_1 a_2 …, a_0 b_0 b_1 …)`, with
constant cocycle `(−1, 1)`.

**(d)** If `g ∈ nV` has table bricks `B`, then `g × id` is the prefix replacement on the bricks
`B × C^{m−n}` with empty words in the last `m − n` coordinates, as in `brin-thompson-nv-embeds-in-mv`.
So `c(g × id)(x, y) = (c(g)(x), 0, …, 0)`, and `J(g × id)(x, y) = J(g)(x)`. Hence `g ∈ M_n` implies
`g × id ∈ M_m`.

## Item 4 (rank-one split of the cocycle half)

**Coset intersection.** Let `H_1, H_2 ≤ G`. If `x ∈ gH_1 ∩ hH_2`, then `gH_1 = xH_1` and
`hH_2 = xH_2`, so `gH_1 ∩ hH_2 = x(H_1 ∩ H_2)`. So a left coset of `H_1` and a left coset of `H_2`
meet in the empty set or in one left coset of `H_1 ∩ H_2`.

**Sums.** Let `ψ_1, ψ_2 ≥ 0` with `ψ_i` proper modulo `H_i`. Fix `R`. Then
`{ψ_1 + ψ_2 ≤ R} ⊆ {ψ_1 ≤ R} ∩ {ψ_2 ≤ R} ⊆ (⋃_a g_a H_1) ∩ (⋃_b h_b H_2) = ⋃_{a,b} (g_a H_1 ∩ h_b H_2)`,
a finite union of left cosets of `H_1 ∩ H_2`. A sum of cnd functions is cnd. So `ψ_1 + ψ_2` is a
cnd function proper modulo `H_1 ∩ H_2`.

**Converse.** If `H' ≤ H`, each left coset of `H'` lies in a left coset of `H`, so properness
modulo `H'` implies properness modulo `H`.

**Conclusion.** Supplement (a) of `brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`
says that `P1 ∧ P2` is exactly "some cnd function on `nV` is proper modulo `K`". By item 1,
`K = M_n ∩ D`. By the two previous paragraphs, a cnd function proper modulo `K` exists iff cnd
functions proper modulo `M_n` and modulo `D` exist. This is `P1 ∧ P2 ⟺ Q_J ∧ Q_D`.

## Item 5 (two further splits of the goal)

This is `haagerup-splits-as-coset-plus-subgroup-properness`, applied to the countable group `nV`
with `H = M_n`, and again with `H = D`.

## Item 6 (what the halves see)

**(a)** Let `n ≥ 2`, let `x_0 ∈ V` be the element `0y ↦ 00y`, `10y ↦ 01y`, `11y ↦ 1y` of Step 8
of `brin-thompson-nv-haagerup-iff-cocycle-kernel-domination-proof`, and let
`z = id × x_0 × id^{n−2}`. So `c(z^k)(x) = (0, c_V(x_0^k)(x_2), 0, …, 0)`, where `c_V` is the
exponent cocycle of `V = 1V`. Step 8 there gives `c_V(x_0^M) = M` on `[0]` for `M ≥ 1`; and
`c_V(x_0^{−M}) = −c_V(x_0^M)∘x_0^{−M}` is then not identically `0` either. So `c_V(x_0^k) ≢ 0` for
every `k ≠ 0`. Then
`J(z^k) = c_V(x_0^k)∘pr_2 ≢ 0`, so `z^k ∉ M_n`. Also the first coordinate of `c(z^k)` is `0` while
the second is not identically `0`, so `c(z^k)` is not pointwise in `Z(1,…,1)`, and `z^k ∉ D`. Now
`z^M H = z^N H` iff `z^{N−M} ∈ H`. So the powers `z^M` lie in pairwise distinct left cosets of `M_n`
and of `D`.

By `brin-thompson-nv-fibre-elements-are-cubically-elliptic` (item 1: `z` is a fibrewise element up
to a coordinate permutation), every wall count `ℓ` is bounded on `⟨z⟩`, say by `R`. Then `{ℓ ≤ R}`
meets infinitely many left cosets of `M_n`, and of `D`. So `ℓ` is proper modulo neither.

**(b)** A bounded function `φ` is proper modulo `H` only if `G = {φ ≤ sup φ}` is a finite union of
cosets of `H`, i.e. only if `[G : H] < ∞`. By (a), `M_n` and `D` have infinite index for `n ≥ 2`.
A cnd function `‖b‖²` coming from a cocycle `b` into a gap-class representation is bounded, since
`b` is a coboundary by `nv-gap-class-cocycles-are-coboundaries`. So it is proper modulo neither
subgroup.

**(c)** An element `h^{P,j} ∈ A_P^{(j)}` acts on each `B ∈ P` by the chart conjugate of `h_B` in
coordinate `j` only. So `c(h^{P,j})` is `c_V(h_B)` in coordinate `j` and `0` in the other
coordinates, and `J(h^{P,j}) = c_V(h_B)` on `B`. If `h^{P,j} ∈ M_n`, then every `c_V(h_B) ≡ 0`, so
`c(h^{P,j}) ≡ 0` and `h^{P,j} ∈ K`.

*The Maharam wall.* On `Ω = C^n × Z` with measure `μ = λ ⊗ counting`, let `g ∈ M_n` act by
`g(x, t) = (gx, t − c(g)(x)_1)`. The cocycle identity gives
`g(h(x, t)) = (ghx, t − c(h)(x)_1 − c(g)(hx)_1) = (gh)(x, t)`, so this is an action. It preserves
`μ`, because `g` preserves `λ` (item 3(a)) and acts by translations on the `Z` fibres. Let
`A = C^n × {t ≥ 0}`. Then `gA = {(y, s) : s ≥ −c(g)(g^{-1}y)_1}`, and the fibre of `gA Δ A` over
`y` has `|c(g)(g^{-1}y)_1|` points. So
`μ(gA Δ A) = ∫ |c(g)(g^{-1}y)_1| dλ(y) = ∫ |c(g)(x)_1| dλ(x) < ∞`, using `g_*λ = λ` once more.
Then `β(g) = 1_{gA} − 1_A ∈ L²(Ω, μ)` satisfies `β(gh) = β(g) + g·β(h)` for the Koopman
representation, so it is a 1-cocycle. Hence `ψ_M(g) = ‖β(g)‖² = μ(gA Δ A)` is a cnd function on
`M_n`. For `n = 2` and the baker's map `b`, `c(b^N) ≡ N(−1, 1)` by item 3(c) and the cocycle
identity, so `ψ_M(b^N) = N`.

The remark on `nV` in the target is quoted from the Attempts of
`brin-thompson-groups-nv-lack-property-t` and is not part of what this route proves.
