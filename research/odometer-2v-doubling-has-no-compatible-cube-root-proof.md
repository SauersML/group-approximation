---
rg: 2
id: odometer-2v-doubling-has-no-compatible-cube-root-proof
kind: route
title: Roots of s commute with s and so are integer skew products over the second coordinate; the doubling equation turns the cocycle into a carry recursion that never terminates at (10)^∞
target: odometer-2v-doubling-has-no-compatible-cube-root
requires:
  - odometer-2v-is-fp-simple-and-contains-bs12
---

Notation as in the target. Identify a binary word `p = p_0 ... p_(k-1)` with the integer
`Σ p_i 2^i`, and `C` with `Z_2` through `x ↦ Σ x_i 2^i`. Then `τ(x) = x + 1`, and for `n ∈ Z`,
`τ^n(x_0 x') = ((x_0 + n) mod 2) τ^{⌊(x_0 + n)/2⌋}(x')`.

**Step 1 (centralizer).** Let `g ∈ 2V_τ` commute with `s`. Then `g` maps each `s`-orbit closure
onto one. Since `τ` is minimal these closures are the fibres `C × {y}`, so
`g(x, y) = (g_y(x), v(y))`. Each `g_y` commutes with `τ`, and a homeomorphism of `Z_2` commuting
with `x ↦ x + 1` is a translation (`g_y(x) − x` is constant on the dense orbits). So
`g(x, y) = (x + a(y), v(y))` with `a : C → Z_2` continuous. On a rectangle `C(p) × C(w)` of a
defining partition of `g`, with `|p| = k` and `|p'| = k'`, `g` has the form
`(p t, w z) ↦ (p' τ^n t, w' z)`. Comparing first coordinates gives
`p + 2^k t + a(wz) = p' + 2^{k'} (t + n)` for all `t ∈ Z_2`. Subtracting the cases `t = 0` and
`t = 1` gives `2^k = 2^{k'}`, so the pieces keep prefix length (referee fix, bh-ref-t0). So
`a(wz) = p' − p + 2^k n` is an integer, constant on `C(w)`. Hence `a = c` is locally constant with
values in `Z`, and `v ∈ V`. Conversely every such map is in `2V_τ` and commutes with `s`. This is
item 1.

**Step 2 (the equations).** Let `r ∈ 2V_τ` with `r^3 = s`. Then `r` commutes with `s`, so by Step 1
`r(x, y) = (τ^{c(y)} x, v(y))`. Since `τ` has infinite order, `r^3 = s` gives `v^3 = id` and
`c + c∘v + c∘v^2 = 1`. Also `r^2(x, y) = (τ^{e(y)} x, v^2(y))` with `e = c + c∘v = 1 − c∘v^-1`.
Now `u^-1(x_0 x', y) = (x', x_0 y)`. Writing `v(x_0 y) = β_0 β'`,
`u r u^-1 (x_0 x', y) = (β_0 τ^{c(x_0 y)}(x'), β')`. Suppose `u r u^-1 = r^2`. Comparing with
`r^2(x_0 x', y) = (τ^{e(y)}(x_0 x'), v^-1(y))`, and using that `τ` acts freely:
- (A) `v(x_0 y) = b · v^-1(y)` with `b = (x_0 + e(y)) mod 2`;
- (B) `c(x_0 y) = ⌊(x_0 + e(y))/2⌋`.

Put `f = c∘v^-1`, so `e = 1 − f`.

**Step 3 (a closed recursion).** From (A), `v^-1(b w) = ((b + 1 + c(w)) mod 2) · v(w)`. To check:
the preimage of `b w` has the form `x_0 v(w)`, and (A) gives first letter
`(x_0 + 1 − f(v w)) mod 2 = (x_0 + 1 + c(w)) mod 2`. Then (B) applied at the point
`v^-1(x_0 y) = b' v(y)`, with `b' = (x_0 + 1 + c(y)) mod 2` and `f(v y) = c(y)`, gives:
- `c(x_0 y) = ⌊(x_0 + 1 − f(y))/2⌋`;
- `f(x_0 y) = ⌊(b' + 1 − c(y))/2⌋`.

**Step 4 (values in {0,1}).** `c` and `f` are continuous on the compact `C`, so bounded. Let `M` and
`m` be the largest and smallest value taken by `c` or `f`. Every point is `x_0 y`, so Step 3 gives
`M ≤ ⌊(2 − m)/2⌋` and `m ≥ ⌊(1 − M)/2⌋ ≥ −M/2`. If `M ≥ 2`, then `M ≤ (2 + M/2)/2 = 1 + M/4`, which
is false. So `M ≤ 1`, and then `m ≥ ⌊(1 − M)/2⌋ ≥ 0`. With values in `{0,1}`, Step 3 reads:
- `c(x_0 y) = x_0 (1 − f(y))`;
- `f(x_0 y) = (1 − x_0)(1 − c(y))`.

**Step 5 (contradiction).** Step 4 gives `c(0w) = 0`, and `c(11w) = 1 − f(1w) = 1`. Also
`c(10w) = 1 − f(0w) = c(w)` for every `w`. Hence `c((10)^k 0^∞) = 0` and `c((10)^k 1^∞) = 1` for all
`k`. Both sequences converge to `(10)^∞`, so `c` is not continuous there. This contradicts local
constancy (Step 1). So no such `r` exists, which is item 2.

**Item 3.** Let `A ≤ 2V_τ` be normalized by `u`, with `s ∈ A` and `A` isomorphic to a subgroup of
`(Q, +)` in which `s` is divisible by `3`. This holds, for instance, for `A ≅ Z[1/6]` or `A ≅ Q`,
and for the tower `Q_τ ≅ Q`, which contains `s`. Every automorphism of a nonzero subgroup of `Q` is
multiplication by a rational, and `u s u^-1 = s^2` forces that rational to be `2`. So the element
`r ∈ A` with `r^3 = s` satisfies `u r u^-1 = r^2`, which item 2 forbids.

**Item 4.** If `t s t^-1 = s^2 = u s u^-1`, then `u^-1 t ∈ C(s)`, so `t = u g` with `g ∈ C(s)`.
Moreover `t r t^-1 = r^2` iff `g r g^-1 = u^-1 r^2 u`. Here `u^-1 r^2 u` commutes with
`u^-1 s^2 u = s`, so it lies in `C(s)`, and it is again a cube root of `s`.

**Item 5.** Let `r = (c, v) ∈ C(s)` with `r^m = s`, meaning `r(x, y) = (τ^{c(y)} x, v(y))`, and put
`r' = u^-1 r^2 u`. Then `(r')^m = u^-1 s^2 u = s`, and `r'` commutes with `s`
(`[u^-1 h u, s] = u^-1 [h, s^2] u = 1` for `h ∈ C(s)`), so `r' = (c', v') ∈ C(s)`.
- *Orbit structure.* If an `m`-th root `(c, v)` of `s` has a `v`-orbit of size `d`, with `d | m`, then
  `(m/d) · (sum of c over that orbit) = 1`, so `d = m`. So `v` and `v'` act freely, with all orbits of
  size `m`.
- *Conjugating the `y`-parts.* A finite-order element of `V` permutes the cones of some cone
  partition by prefix replacements. For `v` free, every cone-cycle has length `m`: a shorter cycle would
  give a cone mapped to itself by a prefix replacement, hence a fixed point of a proper power of `v`.
  Splitting every cone of one cycle into its two children turns `N` cycles into `N + 1`. So `v` and `v'`
  are both conjugate to cone permutations with the same number of `m`-cycles. Two such permutations are
  conjugate in `V` by any cone bijection that matches cycles position by position. So `w v w^-1 = v'` for
  some `w ∈ V`.
- *Conjugating the cocycles.* For `g = (b, w)`, `g r g^-1 = (c∘w^-1 + b̃∘v' − b̃, v')` with `b̃ = b∘w^-1`.
  The difference `δ = c' − c∘w^-1` has zero sum on every `v'`-orbit, since both sums are `1`. Choose a
  clopen fundamental domain `D` for `v'` (one cone from each cone-cycle). Put `b̃ = 0` on `D` and
  `b̃(v'^i y) = Σ_{j<i} δ(v'^j y)` for `y ∈ D`, `0 < i < m`. This is well defined and locally constant,
  and it solves `b̃∘v' − b̃ = δ`. Then `g r g^-1 = r'`, and `t_r = u g` satisfies `t_r s t_r^-1 = s^2`
  and `t_r r t_r^-1 = u r' u^-1 = r^2`.

**Item 6.** Put `s_j = u^-j s u^j`. Since `u^j(x, y) = (y_(j-1) ... y_0 x, y_j y_(j+1) ...)`, `s_j` adds
`1` to the `2`-adic number with digits `y_(j-1), ..., y_0, x_0, x_1, ...`, least significant first. So
`π(s_j)`, the `y`-part, is `+1 mod 2^j` on the reversed prefix `y_(j-1) ... y_0`. The group
`⟨π(s_j)⟩` acts on `C` with orbits the tail-equivalence classes (sequences differing in finitely many
places).

Let `g = (b, w) ∈ 2V_τ` commute with `S_2`. It lies in `C(s)` by Step 1, and `w` commutes with every
`π(s_j)`. `w` acts on the cone containing `0^∞` by a prefix replacement, so `w(0^∞)` is eventually zero.
Hence `w(0^∞) = ρ(0^∞)` for some `ρ = π(h)`, `h ∈ S_2`. Since `w` and `ρ` both commute with the abelian
group `⟨π(s_j)⟩`, they agree on the orbit of `0^∞`, which is dense. So `w = ρ`. Then `g h^-1 = (b', id)`
commutes with each `s_j`, which gives `b'∘π(s_j) = b'`. A continuous function invariant under a
minimal action is constant, so `g h^-1 = s^n`. Hence `C_{2V_τ}(S_2) = S_2`.

If `t h' t^-1 = h'^2` for all `h' ∈ S_2`, then, since `u s_j u^-1 = s_(j-1) = s_j^2`, `u^-1 t`
centralizes `S_2`. So `t = u h_0` with `h_0 ∈ S_2`. For abelian `A ⊇ S_2`, `h_0` centralizes `A`, so
`t` and `u` act on `A` identically. If `A ≅ Z[1/6]` or `Q` is normalized by `t` acting as `×2`, the
element `r ∈ A` with `r^3 = s` gives `u r u^-1 = r^2`, contradicting item 2.

**Remark (the natural model).** Under `X ≅ {0,1}^Z`, the homeomorphism `r_0(x, y) = (x + 1/3, y)`
satisfies both equations: `r_0^3 = s`, and `u r_0 u^-1` adds `2/3`. So Step 1's integrality is the
whole obstruction. The recursion of Steps 3–4 is the carry automaton of `1/3`, whose `2`-adic digits
repeat `10`.
