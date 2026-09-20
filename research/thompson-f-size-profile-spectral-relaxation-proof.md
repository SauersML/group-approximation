---
rg: 2
id: thompson-f-size-profile-spectral-relaxation-proof
kind: route
title: Data processing reduces size-profile arguments to one law Q on (sizes, pointer); a left-dominant tower with pinned first log-level at every level is cut-blind for every interval count at once, and a uniform count and pointer make Q almost invariant under merge and pointer-right
target: thompson-f-size-profile-spectral-relaxation-has-value-one
requires: []
---

Conventions are those of the target node. All laws are finitely supported. `TV` is total variation, and
`B(ℓ)` for a vector `ℓ = (ℓ_0, ..., ℓ_m)` of nonnegative integers is the product law of independent
uniforms on the dyadic blocks `{2^(ℓ_j), ..., 2^(ℓ_j + 1) − 1}`. `B` is a Markov kernel.

Four standard facts are used.
- (F1) `TV(κ_* p, κ_* q) <= TV(p, q)` for every map or Markov kernel `κ`. So a mixture over a law `p`
  and the same mixture over `q` are within `TV(p, q)`.
- (F2) `TV` of product laws is at most the sum of the coordinate `TV`s.
- (F3) The uniform law on `{x, ..., x + M − 1}` and its translate by `d >= 0` are within `min(1, d/M)`.
- (F4) `BC(p, q) >= 1 − TV(p, q)`, since `1 − BC = (1/2) Σ (√p − √q)² <= (1/2) Σ |p − q|`.
  `BC(κ_* p, κ_* q) >= BC(p, q)` for every map `κ`, by Cauchy–Schwarz on each fibre.

## Step 1. Data processing

`ρ` is injective, so `Σ_v f(v) f(ρ v) = Σ_(y ∈ ρR) √(m(ρ^(−1)y) m(y)) = BC(ρ_* m, m)`, and likewise for
`μ`. `Ψ ∘ g = g̃ ∘ Ψ` gives `Ψ_* g_* m = g̃_* Q`. By (F4),

`⟨f, P f⟩ = (BC(m, ρ_*m) + BC(m, μ_*m))/2 <= (BC(Q, ρ̃_*Q) + BC(Q, μ̃_*Q))/2 = V(Q)`.

Conversely, `V(Q) >= 1 − (t_ρ + t_μ)/2` by (F4), and `V(Q) <= 1` always. So `sup_Q V(Q) = 1` as soon
as `inf_Q (t_ρ + t_μ) = 0`, which Steps 2 to 4 prove.

## Step 2. The tower

Fix integers `N >= 2`, `H >= 1`, `G >= 3` and `R >= 1`. There are levels `t = 1, ..., H + 1`, each with
atoms indexed by `v = 1, ..., N`.

- **Log-levels.** `L^(t)_v = Λ_t − Σ_(1 <= u < v) g^(t)_u`, so `L^(t)_1 = Λ_t` is a constant.
- **Gaps.** `g^(t)_u = G + a^(t+1)_u` for `t <= H` and `u = 1, ..., N − 1`, and `g^(H+1)_u = G`.
- **Atoms.** Given all log-levels of level `t`, the `u^(t)_v` are independent and uniform on
  `{0, ..., 2^(L^(t)_v) − 1}`, and `a^(t)_v = 2^(L^(t)_v) + u^(t)_v`. The `u^(t)` are drawn top-down,
  from `t = H + 1` to `t = 1`.
- **Constants.** `Λ_(H+1) = R + N G`, and `Λ_t = R + N (G + 2^(Λ_(t+1) + 1))` for `t <= H`.

**Properties.**
- (P1) `L^(t)_v >= R` for all `t, v`.
  - At `t = H + 1`, `L_v >= Λ_(H+1) − N G = R`.
  - For `t <= H`, `a^(t+1)_u < 2^(L^(t+1)_u + 1) <= 2^(Λ_(t+1) + 1)`, since log-levels decrease in `v`.
  - So `Σ_(u < N) g^(t)_u < N (G + 2^(Λ_(t+1)+1))`.
- (P2) `L^(t)_(v+1) <= L^(t)_v − G`.
- (P3) Tail bound: for every `p`, `Σ_(v > p) a^(t)_v < Σ_(v > p) 2^(L_v + 1) <= 2^(L_p + 1) Σ_(s >= 1) 2^(−sG)
  <= 2^(L_p − G + 2)`.
- (P4) The level-`t` log-levels are functions of the variables of levels `> t`. The variables `u^(t)_v`,
  given them, are independent of each other and of level `> t`.

**Partial cuts.** A partial cut with `m + 1` intervals is `J_0, ..., J_m`, where the `J_j` are consecutive,
nonempty, and `J_0` starts at `1`. Write `p_j` for the left endpoint of `J_j`, so `p_0 = 1`. A (full) cut
is a partial cut with `J_m` ending at `N`.

## Step 3. Lemma T (multi-count cut-blindness)

Put `ε = 2^(2−G) + G N 2^(−R)`.

**Lemma 1 (one level).** Let `J_0, ..., J_m` be a partial cut at level `t`, and let `c_0, ..., c_m` be
integers in `[0, C]`. Let `S_j = c_j + Σ_(v ∈ J_j) a^(t)_v`. Then the law of `(S_0, ..., S_m)` is within
`(m + 1)(2^(2−G) + C 2^(−R))` of the mixture `E[B(L^(t)_(p_0), ..., L^(t)_(p_m))]`.

*Proof.* Condition on all variables of levels `> t`, which fixes the log-levels of level `t` by (P4). Also
condition on the `u^(t)_v` with `v` not a left endpoint. Then `S_j = a^(t)_(p_j) + d_j`, where
`d_j = c_j + Σ_(v ∈ J_j, v > p_j) a^(t)_v` is now fixed. By (P3) and (P1),
`0 <= d_j < C + 2^(L_(p_j) − G + 2)`. The `a^(t)_(p_j)` are independent and uniform on blocks of size
`2^(L_(p_j))`. By (F3) each coordinate moves by at most `C 2^(−R) + 2^(2−G)` in `TV`, and by (F2) the
vector moves by at most `m + 1` times that. The conditional law of the unshifted vector is
`B(L_(p_0), ..., L_(p_m))`. Average over the conditioning with (F1). ∎

**Lemma 2 (recursion).** Let `t <= H` and `m >= 1`. For a partial cut `J` at level `t` with `m + 1`
intervals, put `J'_i = [p_(i−1), p_i − 1]` for `i = 1..m`. That is a partial cut of `1..N−1` with `m`
intervals and left endpoints `p_0, ..., p_(m−1)`. Then:
- `L^(t)_(p_j) = Λ_t − (F_1 + ... + F_j)`, where `F_i = Σ_(u ∈ J'_i) g^(t)_u = G |J'_i| + Σ_(u ∈ J'_i) a^(t+1)_u`;
- the map `(F_1, ..., F_m) -> (L^(t)_(p_0), ..., L^(t)_(p_m))` is one fixed injective map `φ_m`,
  whatever the cut is.

Both parts are immediate from the definitions. The offsets `G |J'_i|` lie in `[0, G N]`.

**Lemma 3.** For `t <= H + 1` and `0 <= m <= H + 1 − t`, let `Z_t(J)` be the law of the vector
`(L^(t)_(p_0), ..., L^(t)_(p_m))` for a partial cut `J` with `m + 1` intervals at level `t`. Then for two such
cuts, `TV(Z_t(J), Z_t(K)) <= ε m (m + 1)`.

*Proof.* Induction on `m`. If `m = 0`, both laws are the point mass at `Λ_t`. If `m >= 1`, then `t <= H`.
By Lemma 2 and (F1), `TV(Z_t(J), Z_t(K))` is at most the `TV` between the laws of the `F`-vectors. Each
`F`-vector is a level-`(t+1)` interval-sum vector over a partial cut with `m` intervals, with offsets in
`[0, G N]`. By Lemma 1 each is within `m (2^(2−G) + G N 2^(−R)) = m ε` of `E[B(Z_(t+1)(J'))]`, resp.
`E[B(Z_(t+1)(K'))]`. By (F1) and induction, since `m − 1 <= H + 1 − (t + 1)`,
`TV <= 2 m ε + ε (m − 1) m = ε m (m + 1)`. ∎

**Lemma T.** Let `k <= min(H, N − 1)`. For two full cuts `I, I'` of `1..N` into `k + 1` intervals, the laws
of the level-1 interval-sum vectors are within `ε (k + 1)(k + 2)`.

*Proof.* Use Lemma 1 at level 1 with `c = 0`, and Lemma 3 at `t = 1`, `m = k <= H`. This gives
`TV <= 2 (k + 1) 2^(2−G) + ε k (k + 1) <= ε (k + 1)(k + 2)`. ∎

Every level-1 atom is at least `2^R >= 2`, so every interval sum is at least `2`. Since `ε -> 0` as
`G, R -> ∞` with `N` fixed, the parameters can make `ε` as small as wanted. For instance
`G = R = ⌈4 + 2 log2((N + 4)/ε_0)⌉` gives `ε <= ε_0`. Indeed `G 2^(−G) <= 2^(−G/2)` for `G >= 4`, so
`ε <= (N + 4) 2^(−G/2) <= (N + 4) ε_0 / (4 (N + 4)) <= ε_0`.

## Step 4. The law Q_W and the two total variations

Fix `W >= 1`. Put `N = 2W + 1`, `H = 2W`, and choose `G, R` with `ε (2W + 1)(2W + 2) <= 1/W`. Let
`a = a^(1)` be the level-1 atoms.

For `w ∈ {W, ..., 2W}`, the **standard cut** `C_w` has intervals `{1}, ..., {w}, {w + 1, ..., N}`. It has
`w + 1` intervals, and the last one is nonempty since `w + 1 <= N`. Let `σ_w` be the law of its sum vector
`(s_0, ..., s_w)`. For a vector `s`, let `pad(s) = (s_0, ..., s_w, 1, 1, ...)`.

**Definition.** Draw `w` uniform on `{W, ..., 2W}`, `s ~ σ_w`, and `i` uniform on `{0, ..., W − 1}`,
all independent given `w`. `Q_W` is the law of `(pad(s), i) ∈ X`.

**Pointer-right.** `ρ̃_* Q_W` is the same law with `i` uniform on `{1, ..., W}`. The size part and the
pointer are independent in both laws, and the size parts agree. So `TV(Q_W, ρ̃_* Q_W) = 1/W` by (F2) and
(F3).

**Merge.** Fix `w` and `i`. Since `i <= W − 1 < w`, both `n_i` and `n_(i+1)` lie among the first `w + 1`
sizes. Then `μ̃(pad(s), i) = (pad(s'), i)`, where `s'` is the sum vector of the cut `C_w^(i)`. That cut
replaces the `i`-th and `(i+1)`-th intervals of `C_w` by their union. It is a full cut of `1..N` into
`w` intervals, with `k = w − 1 <= min(H, N − 1)`. By Lemma T, the law of `s'` is within
`ε w (w + 1) <= 1/W` of `σ_(w−1)`. Mix over `(w, i)` with (F1). Then `μ̃_* Q_W` is within `1/W` of the law
`Q'` in which:
- `w'` is uniform on `{W − 1, ..., 2W − 1}`;
- `s ~ σ_(w')`;
- `i` is uniform on `{0, ..., W − 1}`.

Here `σ_(W−1)`, the standard cut into `W` intervals, is defined by the same formula, and `k = W − 1` is
allowed.

`Q_W` and `Q'` are the same kernel `w -> law of (pad(s), i)` applied to two uniform laws on `W + 1`
consecutive integers, shifted by one. Those are within `1/(W + 1)`. By (F1),
`TV(Q_W, μ̃_* Q_W) <= 1/W + 1/(W + 1) <= 2/W`. ∎

**Words.** For a word `g = g_1 ... g_r` in `ρ, μ`, the pushforward `g̃_*` is a composition of maps. By the
triangle inequality and (F1), `TV(Q_W, g̃_* Q_W) <= Σ_j TV(Q_W, g̃_j,* Q_W) <= 2r/W`.

## Step 5. Conclusion

`V(Q_W) >= 1 − (1/W + 2/W)/2 = 1 − 3/(2W) -> 1`. So the supremum of the relaxation is `1`, and every bound
that follows from Step 1 alone is at best `⟨f, P f⟩ <= 1`. ∎

**Checks of the parameter bookkeeping.**
- Lemma 3 needs `m <= H + 1 − t` at `t = 1`, that is `k <= H = 2W`. The counts used are `k = w <= 2W` and
  `k = w − 1`. ✓
- Lemma 1 at level `t + 1` uses atoms `1..N − 1` of level `t + 1`, and those exist. ✓
- Realizability: every `(n, i) ∈ X` is `Ψ` of some forest. `Q_W` is supported on `X`, since all sizes
  are `>= 1` and the sequence is eventually `1`. ✓
- The size of the numbers is irrelevant to the theorem. The level-1 atoms are towers of `2`s of height
  about `H + 1`. That is where the doubly exponential and Fibonacci conclusions are met.

## Why the fixed-count tower lemma does not suffice

`thompson-f-tower-size-laws-have-zero-defect` absorbs the last log-level with a height `λ`, uniform on a
window much longer than the log-width of the cluster. With `w + 1` intervals the recursion ends after
`w + 1` stages at that uniform coordinate. For a cut into fewer intervals, the stage structure of a law
built for `w + 1` intervals does not end at the uniform coordinate, so blindness across counts would need
a separate argument. Pinning `L_1 = Λ_t` at every level makes the recursion end at a point mass for every
count. That is the only new ingredient, and it is exactly what a merge, which lowers the count, requires.
