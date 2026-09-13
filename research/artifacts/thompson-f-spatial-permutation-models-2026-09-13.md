# Structured permutation models for Thompson's F (2026-09-13)

**Verdict: no witness, and a theorem for why.** Families built on `F`'s own action (dyadic
points, dyadic cones, finite configurations, the Cantor set) fall into two regimes:
- the generators stay off the true action on a fixed fraction of points, and then relator defect
  stays large;
- or they follow the action on all but a `δ` fraction, and then `d(AB, BA) ≤ 4δ + k sqrt(6δ)`.

The bound is proved in §2. §3 gives exact profiles of both regimes. Generic perturbations of
commuting pairs pay about twice their separation in relator defect.

## 1. Conventions

- `x_0 = t/2` on `[0,1/2]`, `t - 1/4` on `[1/2,3/4]`, `2t - 1` on `[3/4,1]`.
  `x_1 = t` on `[0,1/2]`, `t/2 + 1/4` on `[1/2,3/4]`, `t - 1/8` on `[3/4,7/8]`, `2t - 1` on `[7/8,1]`.
- Words are compositions of maps, and the last letter acts first. With this convention the
  relators `R_1 = [ab^-1, a^-1ba]` and `R_2 = [ab^-1, a^-2ba^2]`, with `[x,y] = x^-1 y^-1 x y`, hold
  for `a = x_0`, `b = x_1`.
  - **Certificate.** Each generator breaks only at points of `D_3 = {k/8}`. Its pieces are
    `2^e t + β` with `e ∈ {-1,0,1}` and `β ∈ D_3`, so for `s ≥ 3` it maps `D_s = {k/2^s}` into
    `D_(s+1)`, and so does its inverse. A word of length `ℓ` therefore breaks only at `D_(ℓ+2)`.
    `R_1` and `R_2` (lengths 10 and 14) fix every point of `D_17`, so both are the identity map.
  - When the first letter acts first, they fail at sampled points.
- `c = x_0 x_1 x_0^-1 x_1^-1`. It fixes `[0,1/4] ∪ [3/4,1]` pointwise.
  - For `s ≤ 1/4`: `x_1^-1 s = s`, `x_0^-1 s = 2s ≤ 1/2`, `x_1(2s) = 2s`, `x_0(2s) = s`.
  - For `s ≥ 3/4` the chain is `s ↦ (s+1)/2 ↦ (s+3)/4 ↦ (s+1)/2 ↦ s`.
- `d(AB, BA)` is the fraction of points moved by `ABA^-1B^-1`, because `ABu ≠ BAu` exactly when
  `ABA^-1B^-1` moves `BAu`.

## 2. Theorem: spatial models almost commute

**Setting.**
- `Ω` is an `F`-set with an equivariant map `p = (p_1, ..., p_k) : Ω → [0,1]^k` such that `c`
  fixes every `ω` with no `p_i(ω)` in `K = [1/4, 3/4]`.
- `S` is finite, `π : S → Ω` is injective, and `A, B ∈ Sym(S)`.
- `A` is *bad* at `s` if `π(As) ≠ x_0 π(s)`, and `B` is bad at `s` if `π(Bs) ≠ x_1 π(s)`. Each of
  `A, B` is bad at no more than `δ|S|` points.

**Theorem.** `d(AB, BA) ≤ 4δ + k sqrt(6δ)`. Also `d(w(A,B), 1) ≤ |w| δ` for every word `w` with
`w(x_0, x_1) = 1`; this covers both relators.

**Proof.**
1. **Word paths.** `A^-1` is bad at `t` (`π(A^-1 t) ≠ x_0^-1 π(t)`) only if `A` is bad at `A^-1 t`,
   so each letter of `a^±1, b^±1` has at most `δ|S|` bad points. Let `w` have length `ℓ` and let
   `W_i` be the product of its last `i` letters, evaluated at `(A,B)`. Step `i+1` of the path of `s`
   is bad only if `W_i s` lies in that letter's bad set, and `W_i` is injective. So at most `ℓδ|S|`
   points have a bad step. Every other `s` has `π(w(A,B) s) = w(x_0,x_1) π(s)`.
2. **Relators.** If `w(x_0,x_1) = 1`, each good `s` has `π(w(A,B)s) = π(s)`. So `w(A,B)s = s` by
   injectivity.
3. **The window `K` is nearly empty.** Let `ν_i` be the image of the uniform probability on `S`
   under `p_i ∘ π`, a probability measure on `[0,1]`.
   - The points `s` with `p_i π(s) ∈ K` and a good path for `a^j` have measure at least
     `ν_i(K) - jδ`. `A^j` maps them injectively into `{t : p_i π(t) ∈ x_0^j K}`, so
     `ν_i(x_0^j K) ≥ ν_i(K) - jδ`.
   - `x_0^3(3/4) = 1/8 < 1/4`, and `x_0` is increasing, so the sets `x_0^(3j) K`, `j ≥ 0`, are
     pairwise disjoint.
   - For every `N ≥ 1`: `1 ≥ Σ_(j<N) ν_i(x_0^(3j) K) ≥ N ν_i(K) - 3δ N(N-1)/2`. So
     `ν_i(K) ≤ 1/N + 3δ(N-1)/2`.
   - `N = ⌈sqrt(2/(3δ))⌉` gives `ν_i(K) ≤ sqrt(6δ)`. For `δ = 0`, let `N → ∞`.
4. **Commutator.** If `ABA^-1B^-1` moves `s`, then either its path has a bad step (at most `4δ|S|`
   points) or `c` moves `π(s)`. The latter forces `p_i π(s) ∈ K` for some `i` (at most `k sqrt(6δ)|S|`
   points); otherwise `c` fixes `π(s)` and step 2 applies. ∎

**Instances.**
- Points of `[0,1]`: `p = id`, `k = 1`. This covers `D_L`, orbits, and the `x_0`-rays of
  `thompson-f-end-rigid-schreier-graphs-are-amenable`.
- Closed intervals, including dyadic cones and variable-depth tree truncations: `p` = endpoints,
  `k = 2`, since `c[x,y] = [cx, cy]`.
- `k`-point configurations, with `p` the sorted tuple.
- The Cantor set with the prefix-replacement action: `p` = binary value, `k = 1`. A word with value
  outside `K` lies in the cylinder `00` or `11`, over `[0,1/4]` or `[3/4,1]`, where `c` acts as the
  identity.

**Consequence.** If `d(AB, BA) ≥ ε`, then every such labelling has `δ ≥ min(ε/8, ε²/(24k²))`.
- If `δ < ε/8`, then `k sqrt(6δ) > ε/2`, which is the second bound.
- Spatial almost-solutions exist: `δ → 0` forces relator defect `→ 0`. None of them separates.

## 3. Exact profiles

An MSI compute node, python3 with numpy. The script and log are in
`thompson-f-spatial-permutation-models-2026-09-13-search/`: `fmodels.py`, `fmodels.log`. Every
model takes the true map where the image stays in `S`, and matches the leftover points to the missed
points, in sorted order or at random.

### 3.1 Truncations: δ is pinned away from 0

- **Why truncation fails.** On `D_L`, `x_0` leaves `D_L` exactly at the odd `k ≤ 2^(L-1)` (it halves
  there). That is `2^(L-2)` points, so `δ_A = 2^(L-2)/(2^L - 1) → 1/4`.
- `x_1` leaves at the odd `k` with `2^(L-1) < k < 3·2^(L-2)`, so `δ_B → 1/8`.
- Cones of depth `0..L`, which is prefix replacement on words of length `≤ L`, have the same limits.
  Shallow bands of depths are worse.
- A reservoir of size `o(n)` cannot absorb a quarter of the points. By §2, any repair that drives
  `δ → 0` also drives the separation to 0.

| family | n | δ_A | δ_B | d(R_1) | d(R_2) | d(AB,BA) |
|---|---|---|---|---|---|---|
| points `D_8`, sorted | 255 | 0.2510 | 0.1255 | 0.5333 | 0.7059 | 0.6863 |
| points `D_16`, sorted | 65535 | 0.2500 | 0.1250 | 0.5313 | 0.7031 | 0.6875 |
| points `D_16`, random | 65535 | 0.2500 | 0.1250 | 0.5313 | 0.6555 | 0.6875 |
| cones depth 0..14, sorted | 32767 | 0.2500 | 0.1250 | 0.5313 | 0.7032 | 0.6875 |
| cones depth 10..14, random | 31744 | 0.2661 | 0.1331 | 0.5540 | 0.6767 | 0.6939 |
| cones depth 13..14, random | 24576 | 0.4167 | 0.2083 | 0.6722 | 0.7602 | 0.7655 |
| `D_10` × 8 copies, random fibre permutation on `A` | 8184 | 0.2502 | 0.1251 | 0.6132 | 0.7432 | 0.7417 |

### 3.2 x_0-rays: δ → 0, and the commutator dies with it

`S = {x_0^j(t) : t ∈ D_6 ∖ {0,1}, 0 ≤ j < M}`, with sorted matching.

| M | n | δ_A | δ_B | d(R_1) | d(R_2) | d(AB,BA) | `4δ + sqrt(6δ)` |
|---|---|---|---|---|---|---|---|
| 8 | 175 | 0.0914 | 0.0457 | 0.2400 | 0.2457 | 0.2457 | 1.1064 |
| 32 | 559 | 0.0286 | 0.0143 | 0.0751 | 0.0769 | 0.0769 | 0.5289 |
| 128 | 2095 | 0.0076 | 0.0038 | 0.0201 | 0.0205 | 0.0205 | 0.2446 |
| 512 | 8239 | 0.0019 | 0.0010 | 0.0051 | 0.0052 | 0.0052 | 0.1157 |

All three columns decay like `2.6/M`. The theorem's `sqrt δ` bound is not sharp for these windows.

### 3.3 Perturbed commuting pairs: defect ≈ 2 × separation

Torus shifts on `Z_256 × Z_256`, with `B` composed with `⌊f n⌋` random transpositions.

| f | d(R_1) | d(R_2) | d(AB,BA) |
|---|---|---|---|
| 0.001 | 0.00789 | 0.00789 | 0.00395 |
| 0.01 | 0.07689 | 0.07663 | 0.03914 |
| 0.05 | 0.33032 | 0.32977 | 0.18181 |

Each relator has four `b`-letters and the commutator word two, and unstructured errors do not
cancel. This is an observation, not a bound.

## 4. The exact gap

- **Excluded.**
  - Every labelling that follows an `F`-set over `[0,1]^k` with `δ → 0` (§2).
  - Truncations, whose `δ` is pinned near `1/4`, measured with relator defect `≥ 0.53`.
  - Unstructured perturbations of commuting pairs.
- **Still needed.** A witness `(A_n, B_n)` with `d(A_nB_n, B_nA_n) ≥ ε` and relator defect `→ 0`
  must be `min(ε/8, ε²/(24k²))`-far from following `F` on points, intervals, `k`-configurations or
  the Cantor set, under every injective labelling. By `thompson-f-sofic-iff-relator-system-unstable`
  its fixed-point character needs a regular component.
- **What remains.** Labellings by `F`-sets with no equivariant map to any `[0,1]^k` of the kind in
  §2 (for the regular `F`-set, Følner sets exist exactly when `F` is amenable), and models that
  follow no `F`-set at all.
