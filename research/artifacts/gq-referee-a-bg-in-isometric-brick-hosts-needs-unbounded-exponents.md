# Referee report (gq-referee-a, proof-gap lens): BG in isometric brick hosts needs unbounded exponents

**Reviewed:** `bg-in-isometric-brick-hosts-needs-unbounded-exponents` (lane bh-one-relator, cf3b0aad3; the proof is
inline), read on origin/main.

**Verdict: PASS.** Items 1–3 and the consequences hold, and I found no gap in the two places the author asked about.
There are two nits.
- Cited inputs, for the citation lens:
  - the equicontinuity input `baumslag-gersten-equicontinuous-generator-acts-trivially`;
  - Step 1 of `brin-thompson-exponent-cocycle-proof`;
  - the Lipschitz and box-dimension entropy bound;
  - `h(u) ≥ log 2`.

## Item 2: the reading-length step (the author asked about this)
- *Table bricks.* A brick `Π C(p_j)` with every `|p_j| ≥ L` lies in one table brick of `g`.
  - For `y` in it, the table brick of `y` has prefixes `u'_j` of `y_j` with `|u'_j| ≤ L ≤ |p_j|`.
  - So each `u'_j` is a prefix of `p_j`, and the whole brick lies in `Π C(u'_j)` (N1).
- *Extending short prefixes.* If `|p_j| = ℓ^j_m + S^j_m < L`, extend `u_j` by `L − |p_j|` digits of `x_j`.
  - The isometry `η_j` maps a cone of that length onto a cone of the same length, so the image prefix has length
    exactly `L`.
  - Composing with `g`'s table gives a brick map for `g^(m+1)` with isometric sections.
  - The new length is `ℓ^j_m + L − |p_j| = L − S^j_m(x)`. Coordinates are refined independently. So
    `ℓ^j_(m+1) ≤ max(ℓ^j_m, L − S^j_m)`. ✓
- *The bound.* From `ℓ^j_0 = 0` and `S^j_m ≥ −K`, induction gives `ℓ^j_m ≤ L + K` for `m ≥ 0`.
  - `L(g^(−1)) = L(g)`, since the inverse table has the same words.
  - The cocycle identity `S_m(g^(−1), x) = −S_m(g, g^(−m)x)` covers `m ≤ 0`. ✓
- *Equicontinuity.* Put `N = L + K`. On each level-`N` brick, `g^m` is a brick map with range prefixes of length
  `N + S^j_m ≥ N − K`.
  - Points with common prefix lengths `c_j ≥ N` keep common prefix lengths `N + S^j_m + (c_j − N) ≥ c_j − K`, because
    `η_j` is an isometry.
  - So `d(g^m x, g^m y) ≤ 2^K d(x,y)` for `d(x,y) < 2^(−N)`, uniformly in `m ∈ Z`. ✓
- *The contradiction.* The cited node makes `g` trivial.

## Item 3: the Lipschitz constant (the author asked about this)
- *Close points.* `d(x,y) < 2^(−L(f)+1)` means `m(x,y) ≥ L(f)`. So `x` and `y` lie in one table brick, whose words have
  length at most `L(f)`.
  - `f` changes each common prefix length by `|v_j| − |u_j| ≥ −|u_j| ≥ −L(f)`.
  - So `d(fx, fy) ≤ 2^(L(f)) d(x,y)`.
- *Far points.* Otherwise `d(fx, fy) ≤ 1 = diam ≤ 2^(L(f)−1) d(x,y)`.
- So `f` is `2^(L(f))`-Lipschitz (N2). ✓
- *Box dimension.* Radius-`2^(−k)` balls are the level-`k` bricks, of which there are `2^(nk)`. So `dim_B = n`, and the
  cited bound gives `h(f) ≤ nL(f) log 2`.
- *Zero entropy.* `h(g) = h(g^2) = 2h(g)` with `h(g) < ∞` gives 0. `b` is conjugate to `a`, so `h(φ(b)) = h(g)`. ✓

## Item 1 and the consequences
- *Item 1.* The cocycle `δ` is well defined and locally constant.
  - Splitting a coordinate by a digit `c` gives `C(u_jc) → C(v_jh(c))`, with the same length difference and the
    isometric section `h|_c`.
  - Composition adds the differences. So Step 1 of the cited proof applies. ✓
- *Isometric sections in the listed hosts.*
  - `s = τ × id` has `δ ≡ 0`, since the odometer is an isometry.
  - The affine sections `x ↦ p^kx + c` with `p^k ∈ Z_2^×` are isometries of `Z_2`.
  - So by item 2 no `φ` has `φ(a) = s`, and by item 3 and the cited `h(u) ≥ log 2` no `φ` has `φ(b) = u`. ✓

## Nits
- **N1 (item 2).** Add the prefix argument above for "the image brick then lies in one table brick of `g`", and the
  base case `ℓ^j_0 = 0`.
- **N2 (item 3).** In the Lipschitz bound, state that the drop is `|u_j| − |v_j| ≤ |u_j| ≤ L(f)`, and that the far case
  uses `diam(C^n, d) = 1`.
