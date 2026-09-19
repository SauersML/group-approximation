---
rg: 2
id: nv-coordinate-shadow-sets-are-rational-subspaces-proof
kind: route
title: Track each coordinate as a written word followed by an untouched tail of the input; bounded offsets pin both, so the orbit shadow is finite, and offsets add on commuting elements
target: nv-coordinate-shadow-sets-are-rational-subspaces
requires: []
---

Notation is as in the target. Every step is elementary, and no result is imported beyond
(S1)–(S3) of `coordinate-shadows-rigidify-abelian-normalizers-in-nv`, whose proofs are short and
self-contained.

**Tracking lemma.** Let `F` be a finite set of elements of `nV`. Let `D` be the largest prefix
length, `|u_i|` or `|U_i|`, in fixed brick tables of the members of `F`. Let `z ∈ C^n`, and let
`z^0 = z, z^1 = f_1 z^0, …, z^t = f_t z^{t-1}` with `f_s ∈ F`. Fix a coordinate `i`. Suppose
every cumulative offset satisfies `|c_i(f_s ⋯ f_1)(z)| <= β` for `s <= t`. Then for every
`s <= t`,

  `z^s_i = W^s σ^{k^s}(z_i)`  with  `0 <= k^s <= D + β`  and  `|W^s| <= D + 2β`,

where `σ` deletes the first letter, and `|W^s| - k^s = c_i(f_s ⋯ f_1)(z)`.

*Proof.* Put `W^0 = ∅` and `k^0 = 0`. Given `z^s_i = W σ^k(z_i)`, the brick of `f_{s+1}`
containing `z^s` reads a prefix `u` of coordinate `i` with `a = |u| <= D`, and writes `U` with
`|U| <= D`. There are two cases.
- If `a <= |W|`, write `W = uW'`. Then `z^{s+1}_i = UW'σ^k(z_i)`. Put `W^{s+1} = UW'` and
  `k^{s+1} = k`.
- If `a > |W|`, then `u = W·z_i[k+1 .. k+a-|W|]`. Then `z^{s+1}_i = Uσ^{k+a-|W|}(z_i)`. Put
  `W^{s+1} = U` and `k^{s+1} = k + a - |W|`.

In both cases `|W^{s+1}| - k^{s+1} = (|W| - k) + (|U| - a)`. By induction and the cocycle
identity, this is `c_i(f_{s+1} ⋯ f_1)(z)`.

Now `k` changes only in the second case, and there `W^{s+1} = U` has length at most `D`. The
offset bound `|W^{s+1}| - k^{s+1} >= -β` then gives `k^{s+1} <= D + β`. So `k^s <= D + β` for
all `s`, by induction from `k^0 = 0`. Finally `|W^s| <= k^s + β <= D + 2β`. ∎

**Consequence.** Under the hypotheses of the lemma for every `i ∈ J`, the set `{pr_J z^s}` has at
most `Π_{j∈J} (D + β + 1)·2^{D+2β+1}` points. The reason is that `pr_J z^s` is determined by the
pairs `(W^s_j, k^s_j)`, `j ∈ J`, together with `z`.

**(T1), offsets bound shadows.** Take `F = {g}` for forward times and `F = {g^{-1}}` for
backward times. The backward offsets are `c_j(g^{-t})(z) = -c_j(g^t)(g^{-t}z)`, which are bounded
by the same `β`. The Consequence bounds `|pr_J(⟨g⟩z)|` by twice the product, uniformly in `z`.

**(T1), shadows bound offsets.** Let `ω = ω_J(g) < ∞` and `j ∈ J`.
- For fixed `s`, `c_j(g^s)` is locally constant. So its supremum is attained on a nonempty open
  set, and that set contains points whose coordinates are all non-eventually-periodic. Such
  points are dense. So it is enough to bound `|c_j(g^s)(z)|` at such `z`.
- For such `z`, the value `c_j(g^s)(z)` is determined by the point `(g^sz)_j`. Indeed,
  `(g^sz)_j = Wσ^k(z_j)` with `|W| - k = c_j(g^s)(z)`. If also `Wσ^k(z_j) = W'σ^{k'}(z_j)` with
  `|W| - k ≠ |W'| - k'`, then `z_j` would be eventually periodic.
- So `s ↦ c_j(g^s)(z)` takes at most `ω` values. It starts at `0`, and each step changes it by
  at most `D`, since `|c_j(g^{±1})| <= D`.
- An integer walk with steps of size at most `D` that reaches `R` meets each of the intervals
  `[mD, (m+1)D)` with `0 <= mD <= R`. So `R < Dω`.

Hence `β_J(g) <= Dω_J(g)`.

For `J = {1..n}`, (S3) of the source node says that J-boundedness is finite order. So finite order
is equivalent to bounded offsets in every coordinate.

**(T2).** First, `0 ∈ Λ_J`.
- *Additive.* Let `v, w ∈ Λ_J`. Then
  `c_J(x^{t(v+w)})(z) = c_J(x^{tv})(x^{tw}z) + c_J(x^{tw})(z)`,
  which is bounded by `β_J(x^v) + β_J(x^w)` uniformly in `t` and `z`. By (T1), `v + w ∈ Λ_J`.
  Also `-v ∈ Λ_J`, because `⟨x^{-v}⟩ = ⟨x^v⟩`.
- *Saturated.* If `mv ∈ Λ_J` with `m ≠ 0`, then `v ∈ Λ_J`, by (S2).
- A saturated subgroup is determined by its rational span. So `D_J`, which is the set of lines
  `[v]` with `v ∈ Λ_J \ {0}`, equals `P(Λ_J ⊗ Q)`.
- *Uniformity.* Take a basis `b_1, …, b_r` of `Λ_J`. Then
  `x^v = x^{v_1 b_1} ⋯ x^{v_r b_r}`, and the cocycle identity bounds `|c_J(x^v)(z)|` by
  `β' = Σ β_J(x^{b_i})`. Apply the tracking lemma with `F = {x^{±b_i}}`, along the path that
  applies the factors one letter at a time. Every cumulative offset along this path is the offset
  of an element `x^{v'}` with `v' ∈ Λ_J`, so it is at most `β'`. So `pr_J(x^{Λ_J}z)` has
  uniformly bounded size.

**(T3).** By (S1), `x^v` is J-bounded iff `g^{-1}x^vg = x^{Mv}` is. So `v ∈ Λ_J ⇔ Mv ∈ Λ_J`,
which gives `MΛ_J ⊆ Λ_J`. When `M ∈ GL_d(Z)`, apply the same to `M^{-1}`.

Now let `d = 2`. A saturated subgroup has rank `0`, `1` or `2`, and rank `2` means `Λ_J = Z^2`.
Suppose the rank is `1`, so `Λ_J = Zw`. Then every twisting `M` satisfies `Mw ∈ Qw`, so `w` is a
rational eigenvector of `M`.
- A hyperbolic `M ∈ GL_2(Z)` has no rational eigenvector. If `det M = 1`, a rational
  eigenvalue needs `tr² - 4 = s²`, which forces `|tr| = 2`. If `det M = -1`, it needs
  `tr² + 4 = s²`, which forces `tr = 0`, and then the eigenvalues are `±1`. Neither case is
  hyperbolic.
- The normalizer image lies in the stabilizer of the line `Qw`. After a change of basis this is
  `{(ε_1, b; 0, ε_2)}`, which is virtually `Z`.

If `D_J` is finite and nonempty, the rank is `1`, since rank `2` gives all of `P^1(Q)`. So
`D_J` is exactly one point.

**(T4).** Let `g` have infinite order and fix `t`.
- If every point had period at most `t`, then `g^{t!}` would be the identity. So some `z` has
  `z, gz, …, g^tz` pairwise distinct.
- Put `B_i = sup_{0<=s<=t, z'} |c_i(g^s)(z')|` and apply the tracking lemma with `F = {g}`.
  The `t+1` distinct points are determined by the pairs `(W^s_i, k^s_i)`. So
  `t + 1 <= Π_i (D + B_i + 1)·2^{D+2B_i+1}`.
- Take `log_2`, with `B = max_i B_i`. This gives
  `2nB >= log_2(t+1) - n(D+1) - n·log_2(D+B+1)`.
- Split into two cases.
  - If `B >= log_2 t`, the claimed bound holds.
  - Otherwise `log_2(D+B+1) <= log_2(D + log_2 t + 1) = O_g(log log t)`.

  In both cases `B >= (log_2 t)/(2n) - O_g(log log t)`.
- If `g` is J-bounded, the coordinates in `J` contribute a factor that is bounded independently
  of `t`, by (T1). So the same estimate holds with `n` replaced by `n - |J|` and the maximum
  taken over `i ∉ J`.

**Forced shape.** Let `Φ ∈ nV` twist `Z^2` by a hyperbolic `A`.
- By (T3), each `Λ_J` is `0` or `Z^2`.
- If `Λ_J = Λ_{J'} = Z^2`, then `Λ_{J∪J'} = Z^2`, because
  `|pr_{J∪J'} S| <= |pr_J S|·|pr_{J'} S|`. So the union `J_max` of all such `J` has
  `Λ_{J_max} = Z^2`, and `J_max ≠ {1..n}`, by (S3).
- For `i ∉ J_max`, `Λ_{\{i\}} = 0`. Hence every nonzero `x^v` has unbounded `i`-offsets.
- *Upper bound.* The group `⟨Z^2, Φ⟩` is a quotient of `Z^2 ⋊_A Z`, since the kernel of the
  map meets `Z^2` trivially. In `Z^2 ⋊_A Z` one has `|x^{tv}| = O(log t)`, which is the
  standard exponential distortion of the fibre of a Sol lattice. Quotient maps do not increase
  word length. For a finite generating set `S` one also has
  `sup_z |c_i(h)(z)| <= (max_{s∈S} sup|c_i(s)|)·|h|_S`, by the cocycle identity. So the
  offsets of `x^{tv}` are `O(log t)`.
- *Lower bound.* This is (T4), applied with `J = J_max`.

**What this does not reach.** The two open cases are:
- `J_max ≠ ∅`: the whole `Z^2` is uniformly bounded on the `J_max`-coordinates, by (T2). This
  does not split off those coordinates, since the tails of the `J_max`-coordinates are carried
  along at shifting positions.
- `J_max = ∅`: every coordinate has `Θ(log t)` offset growth along every ray. The tracking
  lemma allows this, because `2^{O(log t)}` is polynomial.

Both need a new invariant.
