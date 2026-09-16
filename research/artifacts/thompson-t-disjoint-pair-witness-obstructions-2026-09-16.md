# Witnesses for the disjoint-pair certificate: two candidate classes are dead

Swarm lane `hi-fron-zaremsky-2-01-thompson-f-amena` (frontier angle on
`zaremsky-2-01-thompson-f-amenable`), 2026-09-16. It works on the hole
`thompson-t-has-cstar-simple-subgroup-with-disjoint-pair`: some C*-simple `H ≤ T` contains
nontrivial `a, b` with `supp(a) ∩ supp(b) = ∅` on the circle. It decides nothing about
amenability of `F`.

The map in `zp-thompson-f-nonamenability-certificates-2026-09-13-part2.md`, §3, lists two
concrete sources of C*-simple witnesses that are not circular: free products `A * B`
(Paschke–Salinas) and acylindrically hyperbolic groups with trivial amenable radical
(Dahmani–Guirardel–Osin). Both are ruled out here, unconditionally, by one non-embedding
theorem for `V`:

> **BSD.** `Z^2 ∗ Z` is not a subgroup of Thompson's group `V`
> (Bleak–Salazar-Díaz, arXiv:0911.0979, Theorem 1.2; node
> `z2-free-z-does-not-embed-in-thompson-v`).

Contents.
1. A disjoint pair in `T` generates `Z^2`.
2. Free products (elementary, uses Kurosh).
3. Lemma A: torsion-free elliptic subgroups are free factors in acylindrical actions.
4. Corollary: acylindrically hyperbolic subgroups of `V` contain no `Z^2`.
5. Lemma G: stabilizers of witnesses are non-amenable everywhere.
6. What is left of the hole.

## 1. A disjoint pair in T generates Z^2

Elements of `T` are orientation-preserving homeomorphisms of `S^1`.

**Lemma 1.** Let `a, b ∈ Homeo_+(S^1)` be nontrivial with `supp(a) ∩ supp(b) = ∅`. Then
`ab = ba`, both have infinite order, and `⟨a, b⟩ ≅ Z^2`.

*Proof.*
1. *Commuting.* On `supp(a)` the map `b` is the identity, and `a` preserves `supp(a)`, so
   `ab = ba` there. Symmetrically on `supp(b)`. On the common fixed set both sides are the
   identity.
2. *Infinite order.* `supp(b) ≠ ∅` is fixed pointwise by `a`, so `a` has a fixed point `x`.
   Cutting the circle at `x` makes `a` an increasing homeomorphism `f` of `[0, 1]`. If
   `f^n = id` with `n ≥ 1` and `f(y) > y` for some `y`, then `f^n(y) > y`, and similarly for
   `f(y) < y`. So `f = id` and `a = 1`, a contradiction. Hence `a`, and symmetrically `b`,
   has infinite order.
3. *Rank 2.* Suppose `a^m b^n = 1`. Then `a^m = b^(-n)`. Its support lies in
   `supp(a) ∩ supp(b) = ∅`, so `a^m = 1 = b^n`, and `m = n = 0` by step 2. ∎

Conjugation by any `g ∈ T` maps a disjoint pair to a disjoint pair, since
`supp(g a g^(-1)) = g(supp a)`.

## 2. Free products

**Standard inputs, not re-read.**
- (K) Kurosh subgroup theorem: a subgroup of `A * B` is a free product of a free group and
  of intersections with conjugates of `A` and `B`.
- (N) Normal forms in `A * B`: a product `x_1 x_2 ⋯ x_k` with `k ≥ 1`, each `x_i` in
  `A \ {1}` or `B \ {1}`, and consecutive letters from different factors, is `≠ 1`.
- (TV) `T ≤ V`. It is also stated in the introduction of arXiv:0911.0979v1 ("T ≤ V").

**Proposition 2.** Let `G = A * B` with `A ≠ 1 ≠ B`, and suppose `G` contains a subgroup
isomorphic to `Z^2`. Then `G` contains a subgroup isomorphic to `Z^2 ∗ Z`.

*Proof.*
1. *`Z^2` is conjugate into a factor.* Let `P ≤ G` with `P ≅ Z^2`. By (K), `P` is a free
   product of a free group and of groups `P ∩ g A g^(-1)`, `P ∩ g B g^(-1)`. A nontrivial free
   product `X * Y` is non-abelian (`xy ≠ yx` for `x ∈ X \ {1}`, `y ∈ Y \ {1}`, by (N)), so
   only one factor is nontrivial. `Z^2` is not free, so `P = P ∩ g C g^(-1)` for some
   `g ∈ G` and `C ∈ {A, B}`. Conjugating, assume `P ≤ A`. Otherwise swap the names of `A` and
   `B`. The other factor is still nontrivial.
2. *A free companion.* Choose `β ∈ B \ {1}` and `x ∈ P \ {1}`. `x` has infinite order. Put
   `c = β x β^(-1)`. Then `c` has infinite order.
3. *Injectivity.* There is a homomorphism `φ : P * ⟨t⟩ → G` with `φ|_P = id` and
   `φ(t) = c`. A nontrivial element of `P * ⟨t⟩` that is not in `P` has a reduced form
   `p_0 t^(k_1) p_1 t^(k_2) ⋯ t^(k_n) p_n` with `n ≥ 1`, all `k_i ≠ 0`, `p_1, …, p_(n−1) ≠ 1`,
   and `p_0, p_n ∈ P` possibly trivial. Its image is
   `p_0 · β · x^(k_1) · β^(-1) · p_1 · β · x^(k_2) · β^(-1) ⋯ β · x^(k_n) · β^(-1) · p_n`.
   Here `β^(±1) ∈ B \ {1}`, `x^(k_i) ∈ A \ {1}`, and the `p_i` with `0 < i < n` lie in
   `A \ {1}`. Drop `p_0` or `p_n` if trivial. What remains alternates between the factors
   and has at least 3 letters, so it is `≠ 1` by (N). Nontrivial elements of `P` map to
   themselves. So `φ` is injective and `⟨P, c⟩ ≅ Z^2 ∗ Z`. ∎

**Corollary 2′.** No subgroup of `V` isomorphic to a free product `A * B` with
`A ≠ 1 ≠ B` contains `Z^2`. So no such subgroup of `T` contains a disjoint pair.

*Proof.* Proposition 2 and BSD give the first sentence. Lemma 1 and (TV) give the second. ∎

**Consequence for the hole.** Every nontrivial free product other than `Z/2 * Z/2` is
C*-simple (Paschke–Salinas; not re-read), but none of them inside `T` contains a disjoint
pair. The free-product branch of
`thompson-t-has-cstar-simple-subgroup-with-disjoint-pair` is closed. It was the branch the
2026-09-13 map called "the most concrete target", and the map's candidate
`(Z^2) * Z ↪ T` does not exist. The map also said (part 2, §4) that a proof that no such
subgroup exists "would be evidence for amenability, not a decision". It is neither. It is a
structural fact about `V`, proved without any reference to `F`.

## 3. Lemma A: elliptic torsion-free subgroups are free factors

**Setting.** `S` is a geodesic `δ`-hyperbolic space with Gromov boundary `∂S`, and `(x|y)_o`
is the Gromov product, extended to `S ∪ ∂S` in the usual way. A group `H` acts on `S` by
isometries. The action is *acylindrical* if for every `ε > 0` there are `R(ε), N(ε)` such
that `d(x, y) ≥ R(ε)` implies that at most `N(ε)` elements `g` satisfy `d(x, gx) ≤ ε` and
`d(y, gy) ≤ ε` (Osin, arXiv:1304.1246v4, first paragraph, read 2026-09-16).

**Standard facts, not re-read** (Bridson–Haefliger III.H.1 and III.H.3, Ghys–de la Harpe
ch. 8, de la Harpe, *Topics in geometric group theory*, II.24). `κ` is a constant depending
only on `δ`.
- (H1) `(x|z)_o ≥ min{(x|y)_o, (y|z)_o} − 2δ` for `x, y, z ∈ S ∪ ∂S`.
- (H2) `|(x|y)_o − (x|y)_(o′)| ≤ d(o, o′) + κ`, with `κ = 0` when `x, y ∈ S`.
- (H3) For `x ∈ S`: `(x|b)_o + (x|o)_b = d(o, b)`. For `x ∈ ∂S` the same holds up to `κ`.
- (H4) For `x, y ∈ S`: `d(x, y) = d(o, x) + d(o, y) − 2(x|y)_o`.
- (H5) A loxodromic `g` has two fixed points `g^+ ≠ g^−` in `∂S`, with `g^n o → g^±` as
  `n → ±∞`. There is `M = M(g)` such that `g^m o` lies within `M` of every geodesic
  `[o, g^n o]`, `0 ≤ m ≤ n` (Morse lemma). Independent loxodromics `g, h` have
  `{g^±} ∩ {h^±} = ∅`, and `g h^± ` are the fixed points of `g h g^(-1)`.
- (H6) `z_n → ξ ∈ ∂S` iff `(z_n|ξ)_o → ∞`. Limits are unique, and `(ξ|η)_o = ∞` iff `ξ = η`.
  If `z_n → ξ` and `sup_n d(q z_n, z_n) < ∞` for an isometry `q`, then `qξ = ξ`.
- (H7) If `d(x, x′) ≤ ε` and `d(y, y′) ≤ ε`, points at the same distance `t` from `x` on
  `[x, y]` and from `x′` on `[x′, y′]` are within `4ε + 8δ`. If `(y|y′)_o ≥ t`, the points at
  distance `t` from `o` on `[o, y]` and `[o, y′]` are within `4δ`.
- (H8) Ping-pong: let `Γ_1, Γ_2` be subgroups of a group acting on a set `X`, with
  `|Γ_1| ≥ 3` and `|Γ_2| ≥ 2`. Suppose there are disjoint nonempty `X_1, X_2 ⊆ X` with
  `γ X_2 ⊆ X_1` for all `γ ∈ Γ_1 \ {1}` and `γ X_1 ⊆ X_2` for all `γ ∈ Γ_2 \ {1}`. Then
  `⟨Γ_1, Γ_2⟩ = Γ_1 * Γ_2`.

**Lemma A.** Let `H` act acylindrically on `S` and contain two independent loxodromic
elements. Let `P ≤ H` be a nontrivial torsion-free subgroup with bounded orbits. Then some
loxodromic `h ∈ H` satisfies `⟨P, h⟩ = P * ⟨h⟩`.

Fix `o ∈ S` and `D ≥ diam(P·o)`, so `d(o, po) ≤ D` for all `p ∈ P`.

**Step A1. Boundary stabilizers in P are trivial.** Let `g` be loxodromic and
`ξ ∈ {g^+, g^−}`. Then `Stab_P(ξ) = 1`.

*Proof.* Replacing `g` by `g^(-1)`, let `ξ = g^+`, and put `z_n = g^n o`. Let
`q ∈ Stab_P(ξ)` and fix `m ≥ 0`.
1. `(z_n|ξ)_o → ∞` by (H6). By (H2), `(q z_n|ξ)_o = (q z_n|qξ)_o ≥ (z_n|ξ)_o − D − κ → ∞`.
   By (H1), `(z_n|q z_n)_o → ∞`.
2. Take `n ≥ m` so large that `(z_n|q z_n)_o ≥ d(o, z_m) + M`. Let `w ∈ [o, z_n]` with
   `d(w, z_m) ≤ M`, and `t = d(o, w)`.
3. `q w` is the point at distance `t` from `qo` on `[qo, q z_n]`. Let `w′` be the point at
   distance `t` on `[o, q z_n]`. By (H7), `d(qw, w′) ≤ 4D + 8δ` and `d(w, w′) ≤ 4δ`.
4. So `d(q z_m, z_m) ≤ M + (4D + 8δ) + 4δ + M =: ε_A`, and `d(qo, o) ≤ D ≤ ε_A`. The constant
   `ε_A` does not depend on `q` or `m`.
5. Choose `m` with `d(o, z_m) ≥ R(ε_A)`. By acylindricity `|Stab_P(ξ)| ≤ N(ε_A)`. A finite
   subgroup of the torsion-free group `P` is trivial. ∎

**Step A2. Conjugating away swaps.** Let `g, h` be independent loxodromics and
`h_n = g^n h g^(-n)`, with fixed points `g^n h^±`. For all large `n`, no `p ∈ P \ {1}` maps a
point of `E_n = {g^n h^+, g^n h^−}` into `E_n`.

*Proof.* `p` cannot fix a point of `E_n`, by A1 for `h_n`. Mapping `g^n h^−` to `g^n h^+` is
mapping `g^n h^+` to `g^n h^−` for `p^(-1)`. So suppose, for contradiction, that for
infinitely many `n` some `p_n ∈ P \ {1}` has `p_n g^n h^+ = g^n h^−`. Put `z_n = g^n o`,
`b_n = g^(-n) o` and `T_n = d(o, z_n) = d(o, b_n)`.
1. *Estimate.* `b_n → g^−`, and `g^− ∉ {h^+, h^−}`. By uniqueness of limits (H6),
   `c := sup_n max_± (h^±|b_n)_o < ∞`. Applying `g^n` and (H3),
   `(g^n h^±|z_n)_o = (h^±|o)_(b_n) ≥ T_n − c − κ =: T_n − c_1`.
2. *`p_n` nearly fixes `z_n`.* `(p_n g^n h^+|p_n z_n)_(p_n o) = (g^n h^+|z_n)_o ≥ T_n − c_1`.
   By (H2), `(g^n h^−|p_n z_n)_o ≥ T_n − c_1 − D − κ`. Also `(g^n h^−|z_n)_o ≥ T_n − c_1`,
   so by (H1) `(z_n|p_n z_n)_o ≥ T_n − c_1 − D − κ − 2δ`. Since `d(o, p_n z_n) ≤ T_n + D`,
   (H4) gives `d(z_n, p_n z_n) ≤ 2c_1 + 3D + 2κ + 4δ =: ε_0`.
3. *`p_n` nearly fixes earlier orbit points.* Let `0 ≤ m ≤ n` and `w ∈ [o, z_n]` with
   `d(w, z_m) ≤ M`. `p_n w` sits at distance `d(o, w)` from `p_n o` on
   `[p_n o, p_n z_n]`, so by (H7) `d(p_n w, w) ≤ 4 max(D, ε_0) + 8δ`. Hence
   `d(p_n z_m, z_m) ≤ 2M + 4 max(D, ε_0) + 8δ =: ε_1`. We may take `ε_1 ≥ D`. It does not
   depend on `m` or `n`.
4. *Pigeonhole.* Fix `m_0` with `d(o, z_(m_0)) ≥ R(ε_1)`. For `n ≥ m_0`, `p_n` lies in
   `Q = {u ∈ H : d(o, uo) ≤ ε_1, d(z_(m_0), u z_(m_0)) ≤ ε_1}`, and `|Q| ≤ N(ε_1)`. So one
   `p ∈ P \ {1}` equals `p_n` for infinitely many `n`. By step 3, `d(p z_m, z_m) ≤ ε_1` for
   every `m ≥ 0`. By (H6), `p g^+ = g^+`, so `p = 1` by A1. Contradiction. ∎

**Fixing the axis.** Apply A2 to independent loxodromics `g, h` and fix one large `n`. Put
`k = h_n` and `E = {k^+, k^−}`. Then `k` is loxodromic, and `pξ ≠ η` for all
`p ∈ P \ {1}` and `ξ, η ∈ E`. So `(pξ|η)_o < ∞` by (H6). Let `M = M(k)` be a Morse constant
that works for both `k` and `k^(-1)` in (H5). For `ξ ∈ E` let `s(ξ) = +1` if `ξ = k^+`
and `−1` otherwise, and put `z^ξ_m = k^(s(ξ) m) o`. Then `z^ξ_m → ξ` as `m → ∞`. Also
`T_m := d(o, z^ξ_m)` does not depend on `ξ`, since `d(o, k^(−m) o) = d(k^m o, o)`.

**Step A3. Bad sets are eventually empty.** For `r ≥ 0` put
`B_r = {p ∈ P \ {1} : (pξ|η)_o > r for some ξ, η ∈ E}`. Then `B_r = ∅` for all large `r`.

*Proof.* Put `ε_2 = 4M + 4D + 12δ` and `ε_3 = 2ε_2 + 2D`.
1. *Bad elements shadow the axis.* Let `p ∈ P`, `ξ, η ∈ E` with `(pξ|η)_o > r`, and let
   `m ≥ 0` with `T_m + M ≤ r − 4δ`. For `n` large, `(z^ξ_n|ξ)_o` and `(z^η_n|η)_o` exceed
   `r + D + κ` by (H6). By isometry invariance and (H2),
   `(p z^ξ_n|pξ)_o ≥ (z^ξ_n|ξ)_o − D − κ > r`. Two uses of (H1) give
   `(p z^ξ_n|z^η_n)_o ≥ r − 4δ`.
2. Let `w ∈ [o, z^ξ_n]` with `d(w, z^ξ_m) ≤ M`, and `t = d(o, w)`, so `|t − T_m| ≤ M` and
   `t ≤ r − 4δ`. The point `pw` is at distance `t` from `po` on `[po, p z^ξ_n]`. Let `w′`
   and `w″` be the points at distance `t` from `o` on `[o, p z^ξ_n]` and `[o, z^η_n]`. By
   (H7), `d(pw, w′) ≤ 4D + 8δ` and `d(w′, w″) ≤ 4δ`. Let `v ∈ [o, z^η_n]` with
   `d(v, z^η_m) ≤ M`. Then `|d(o, v) − T_m| ≤ M`, so `d(v, w″) = |d(o, v) − t| ≤ 2M`.
   Altogether `d(p z^ξ_m, z^η_m) ≤ M + (4D + 8δ) + 4δ + 3M = ε_2`.
3. *Finiteness.* Fix `m_0` with `T_(m_0) ≥ R(ε_3)` and put `r_1 = T_(m_0) + M + 4δ`. Let
   `r ≥ r_1`, fix `ξ, η`, and let `p, p′ ∈ P` both satisfy `(pξ|η)_o > r` and
   `(p′ξ|η)_o > r`. Put `u = p′^(-1) p`. Then `d(uo, o) = d(po, p′o) ≤ 2D ≤ ε_3`, and by step
   2 `d(u z^ξ_(m_0), z^ξ_(m_0)) = d(p z^ξ_(m_0), p′ z^ξ_(m_0)) ≤ 2ε_2 ≤ ε_3`. Since
   `d(o, z^ξ_(m_0)) ≥ R(ε_3)`, there are at most `N(ε_3)` such `u` for fixed `p′`. Hence
   `|B_r| ≤ 4N(ε_3)` for `r ≥ r_1`.
4. *Emptiness.* `B_r` decreases in `r`. The finite set `B_(r_1)` gives finitely many finite
   numbers `(pξ|η)_o`. For `r` above `r_1` and above all of them, `B_r = ∅`. ∎

So there is `r_*` with `(pξ|η)_o ≤ r_*` for all `p ∈ P \ {1}` and `ξ, η ∈ E`.

**Step A4. Ping-pong.** Fix `ρ > r_* + D + κ + 2δ` and put
`X_2 = U = {x ∈ S ∪ ∂S : (x|k^+)_o > ρ or (x|k^−)_o > ρ}` and
`X_1 = ⋃_(p ∈ P \ {1}) pU`.
1. *Nonempty.* `k^+ ∈ U`, since `(k^+|k^+)_o = ∞`. So `X_1 ≠ ∅` too, as `P ≠ 1`.
2. *Disjoint.* Suppose `y = px ∈ U` with `p ∈ P \ {1}`, `(x|ξ)_o > ρ` and `(y|η)_o > ρ` for
   some `ξ, η ∈ E`. Then `(y|pξ)_(po) = (x|ξ)_o > ρ`, so `(y|pξ)_o > ρ − D − κ` by (H2).
   By (H1), `(pξ|η)_o ≥ ρ − D − κ − 2δ > r_*`. This contradicts A3.
3. *`P` moves `X_2` into `X_1`.* This holds by definition.
4. *North–south.* Every `y ∈ X_1` satisfies `(y|k^±)_o ≤ ρ`, by step 2. Let `i ≥ 1` and put
   `b = k^(−i) o` and `T = d(o, b)`. Isometry invariance gives
   `(k^i y|k^+)_o = (y|k^+)_b`. As `i → ∞`, `b → k^−`. So eventually `(b|k^−)_o > ρ + 2δ`,
   and then (H1) forces `(y|b)_o ≤ ρ + 2δ`. By uniqueness of limits (H6),
   `c′ := sup_(i ≥ 1) (k^+|k^(−i) o)_o < ∞`. By (H3), `(y|o)_b ≥ T − ρ − 2δ − κ` and
   `(k^+|o)_b ≥ T − c′ − κ`. By (H1) at the base point `b`,
   `(y|k^+)_b ≥ T − max(ρ + 2δ, c′) − κ − 2δ`. Now `T → ∞` as `i → ∞`, since
   `k^(−i) o → k^− ∈ ∂S`. So there is `j_0` with `k^i X_1 ⊆ U` for all `i ≥ j_0`. The same
   argument for `k^(-1)` gives `k^i X_1 ⊆ U` for all `i ≤ −j_0`.
5. *Conclusion.* Put `h = k^(j_0)`. Every `γ ∈ ⟨h⟩ \ {1}` is `k^i` with `|i| ≥ j_0`, so
   `γ X_1 ⊆ X_2`. `P` is infinite, being nontrivial and torsion-free, and `⟨h⟩ ≅ Z`. By
   (H8), `⟨P, h⟩ = P * ⟨h⟩`, and `h` is loxodromic. ∎

**Remarks on Lemma A.**
- Only the independence of the constants `ε_A, ε_0, ε_1, ε_2, ε_3` from `p, m, n` matters.
  The numerical values in (H1) and (H7) depend on the chosen definition of hyperbolicity
  (Osin uses `δ`-thin triangles). They can be replaced by any constants depending only on
  `δ` and `D`.
- Torsion-freeness is used only in A1, to make finite stabilizers trivial. Some hypothesis
  of this kind is needed. `Z/2 × F_2` acts acylindrically on the Cayley tree of `F_2`
  through the projection, since the kernel is finite. `P = Z/2` is elliptic and central,
  so `⟨P, h⟩` is never `P * ⟨h⟩`.
- No novelty is claimed. Statements of this type are close to the small-cancellation and
  free-product results of Dahmani–Guirardel–Osin and Abbott–Dahmani. The abstract of
  arXiv:1610.04143v2 (Abbott–Dahmani, read 2026-09-16) states its property `P_naive` for
  elements and hyperbolically embedded subgroups, not for elliptic subgroups, so this lane
  wrote the proof out rather than importing it.

## 4. Corollary: acylindrically hyperbolic subgroups of V contain no Z^2

**Imported, verbatim from Osin, arXiv:1304.1246v4** (PDF fetched and text extracted locally
on 2026-09-16):
- Theorem 1.1: "Let G be a group acting acylindrically on a hyperbolic space. Then G
  satisfies exactly one of the following three conditions. (a) G has bounded orbits.
  (b) G is virtually cyclic and contains a loxodromic element. (c) G contains infinitely
  many independent loxodromic elements."
- Definition 1.3 with Theorem 1.2: "We call a group G acylindrically hyperbolic if it
  satisfies either of the equivalent conditions (AH1)–(AH4)", where "(AH2) G admits a
  non-elementary acylindrical action on a hyperbolic space".
- After Theorem 1.1: "If the action is acylindrical, non-elementarity is equivalent to
  condition (c) from Theorem 1.1."
- Corollary 6.9: "Suppose that a group G acts acylindrically on a hyperbolic space S. Then
  there exists N ∈ N such that for every loxodromic element g ∈ G, the centralizer C_G(g)
  contains a cyclic subgroup of index at most N."

In Osin's paper hyperbolic spaces are geodesic (his definition: "S is δ-hyperbolic if it is
geodesic and for any geodesic triangle ...").

**Corollary 4.** Let `G` be a group that does not contain `Z^2 ∗ Z`. Then no acylindrically
hyperbolic subgroup of `G` contains `Z^2`. In particular:
- (V) no acylindrically hyperbolic subgroup of `V` contains `Z^2`;
- (T) no acylindrically hyperbolic subgroup of `T` contains a disjoint pair.

*Proof.* Let `H ≤ G` be acylindrically hyperbolic. By (AH2), `H` acts non-elementarily and
acylindrically on a hyperbolic space `S`, so `H` contains independent loxodromics. Suppose
`P ≤ H` with `P ≅ Z^2`.
1. The restricted action of `P` on `S` is acylindrical, directly from the definition.
2. `P` is not virtually cyclic, so case (b) of Theorem 1.1 fails for `P`.
3. If `P` contains a loxodromic `x`, then `P ≤ C_H(x)`, since `P` is abelian. By Corollary
   6.9, `C_H(x)` is virtually cyclic, and so is its subgroup `P`. This is false. So case (c)
   fails for `P`.
4. Hence `P` has bounded orbits. `P` is nontrivial and torsion-free. Lemma A gives a
   loxodromic `h ∈ H` with `⟨P, h⟩ = P * ⟨h⟩ ≅ Z^2 ∗ Z`, a contradiction.

(V) follows from BSD. (T) follows from (V), (TV) and Lemma 1. ∎

**Consequences.**
- `T` and `V` are not acylindrically hyperbolic, since both contain `Z^2`.
- The acylindrically hyperbolic branch of the hole is closed. The 2026-09-13 map
  (part 2, §3.4) said "No candidate known". There is none.
- More generally, if `H ≤ V` acts acylindrically on a hyperbolic space and contains `Z^2`,
  then the action is elementary: it has bounded orbits or `H` is virtually cyclic.

## 5. Lemma G: every stabilizer of a witness is non-amenable

**Lemma G.** Let `H` be a group with `C*_r(H)` simple, acting on a set `X`, and let
`a, b ∈ H \ {1}` with `supp_X(a) ∩ supp_X(b) = ∅`, where `supp_X(g) = {y : gy ≠ y}`. Then
`Stab_H(y)` is non-amenable for every `y ∈ X`.

*Proof.* This is the mechanism of Theorem D (part 2, §2), localized at one orbit.
1. `x = (1 − a)(1 − b) ∈ C[H]` is nonzero. In `λ(x)δ_1 = δ_1 − δ_a − δ_b + δ_(ab)` the
   coefficient of `δ_a` is `−1` or `−2`, because `a ≠ 1` and `ab ≠ a`.
2. Fix `y ∈ X` with `K = Stab_H(y)`, and let `π` be the permutation representation on
   `ℓ^2(Hy) ≅ ℓ^2(H/K)`. For `z ∈ Hy`, either `bz = z` and `π(1 − b)δ_z = 0`, or
   `z, bz ∈ supp_X(b)`. In the second case `a` fixes `z` and `bz`, so
   `π(1 − a)(δ_z − δ_(bz)) = 0`. Hence `π(x) = 0`.
3. Suppose `K` is amenable. Then `1_K ≺ λ_K`, and induction preserves weak containment
   (Fell), so `π = Ind_K^H 1_K ≺ Ind_K^H λ_K = λ_H`. So `π` extends to a unital
   *-representation of `C*_r(H)`. It is injective by simplicity, but it kills `x ≠ 0`. ∎

For `X = S^1` and `H ≤ T`, call `H` a *witness* if `C*_r(H)` is simple and `H` contains a
disjoint pair.

**(G1) A witness contains an explicit non-amenable subgroup of F.** `Stab_H(0) = H ∩ F`,
since `Stab_T(0) = F` (the only input about `F` used by Theorem D). So `H ∩ F` is
non-amenable. The same holds for `H ∩ g F g^(-1)` for every `g ∈ T`, and for `Stab_H(y)` at
non-dyadic `y`.

**(G2) The stabilizers have no free subgroups.** Cutting `S^1` at `y`, every element of
`Stab_T(y)` becomes a piecewise linear homeomorphism of `[0, 1]` with finitely many
breakpoints. So `Stab_H(y) ≤ PL_+([0, 1])`, which has no non-abelian free subgroup (node
`pl-plus-interval-has-no-non-abelian-free-subgroups`, Brin–Squier). Each `Stab_H(y)` is
non-amenable without free subgroups.

**(G3) No witness is linear.** Suppose `H ≤ GL_n(K)` for a field `K`. Amenability is
determined by finitely generated subgroups, so some finitely generated `L ≤ H ∩ F` is
non-amenable. By the Tits alternative (J. Tits, *Free subgroups in linear groups*, J.
Algebra 20 (1972); not re-read), `L` contains a non-abelian free subgroup or is virtually
solvable. It is not virtually solvable, since it is non-amenable. So it contains a free
subgroup, contradicting (G2). The same argument excludes witnesses inside any group whose
finitely generated subgroups satisfy the Tits alternative "free subgroup or amenable".

**No novelty.** Lemma G is the Haagerup–Olesen argument. (G1)–(G3) are short consequences.
Their use here is as filters on candidate witnesses.

## 6. What is left of the hole

A witness `H ≤ T` must have all of the following properties.
1. `C*_r(H)` is simple, and `H` contains a disjoint pair, hence `Z^2` (Lemma 1).
2. `H` is not a free product of two nontrivial groups (Corollary 2′).
3. `H` is not acylindrically hyperbolic (Corollary 4).
4. Every point stabilizer `Stab_H(y)`, `y ∈ S^1`, is non-amenable and has no free subgroup.
   In particular `H ∩ F` is non-amenable (G1, G2).
5. `H` is not linear over any field (G3).

**Status of the candidate classes of part 2, §3.**

| Class | Status |
|---|---|
| `H = T` | circular (Le Boudec–Matte Bon, Theorem 1.6, as recorded in part 2) |
| micro-supported subgroups with non-amenable rigid stabilizers | circular (part 2, §3.2) |
| free products `A * B` | closed by Corollary 2′ |
| acylindrically hyperbolic, trivial amenable radical | closed by Corollary 4 |
| linear groups with trivial amenable radical | closed by (G3) |

**Not excluded.**
- *Strongly faithful tree actions that are not acylindrical* (de la Harpe–Préaux, Powers
  groups; not re-read). Amalgams `A *_C B` and HNN extensions whose edge groups have large
  intersections with their conjugates evade the Kurosh argument of §2. By (3), they must
  also evade every acylindricity criterion for tree actions.
- *C*-simple groups without a recognizable hyperbolic structure*, for example groups shown
  C*-simple through Kennedy's criterion (no amenable uniformly recurrent subgroup; not
  re-read). By (4), such a proof must show at least that the stabilizers of the circle
  action are non-amenable.

**Reading.** Lemma G turns every witness into an explicit non-amenable subgroup of `F`,
namely `H ∩ F`, without free subgroups. So the certificate route does not avoid exhibiting a
non-amenable subgroup of `F`. It proposes to certify non-amenability of `H ∩ F` through
C*-simplicity of an overgroup. The three closed classes share one feature: their
C*-simplicity comes from free-group dynamics. In the free-product and acylindrical cases
these dynamics produce `Z^2 ∗ Z`. In the linear case they produce a free subgroup of a
stabilizer. Both are forbidden. The part 2, §4 reading ("a proof
that no such subgroup exists would be evidence for amenability") does not apply to these
closures. They are unconditional facts about `V`, `PL_+([0, 1])` and linear groups.

**Next tries.**
1. Decide whether a group `H ≤ V` with a minimal, strongly faithful, non-acylindrical action
   on a tree can contain `Z^2` in a vertex group. The test case is an amalgam
   `A *_C B` with `Z^2 ≤ A` and `C` meeting `Z^2` in a nontrivial subgroup.
2. Apply Lemma G to other `H`-sets. For example, put `H^0_y = {h ∈ H : h = 1 near y}`.
   On `H/H^0_y`, the support of `g ∈ H` is `{u H^0_y : uy ∈ closure(supp g)}`. So if
   `supp(a)` and `supp(b)` have disjoint closures, Lemma G makes every germ stabilizer
   `H^0_y` non-amenable.
3. Look for a C*-simplicity criterion that is not witnessed by free-group dynamics and
   applies to subgroups of `T`. Candidates are boundary actions with a topologically free
   factor. Every action of a witness on `S^1` fails topological freeness, since `a` fixes
   the open set `supp(b)` pointwise.
