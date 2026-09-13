---
rg: 2
id: density-random-no-quotients-below-exp-k-letter-swap-proof
kind: route
title: Swap a middle letter inside a fixed window, then union-bound over simple groups by order
target: density-random-groups-no-finite-quotients-below-exp-k
requires: [finite-simple-groups-at-most-two-per-order, density-random-group-hyperbolic-kazhdan-with-positive-b2]
artifacts:
  - research/artifacts/solve-hyperbolic-rf-2026-09-13.md
  - experiments/hyperbolic-rf/density_quotient_checks.py
---

Notation as in the target. Words are read cyclically, and positions are `1,…,L`.

## Step 0: transfer matrix

Index `2m × 2m` matrices by `A`. Put `T_(xy) = 1` if `y ≠ x^{-1}` and `0` otherwise;
let `J` be all ones and `P` the permutation matrix of inversion. Then:
- `T = J − P`, with `PJ = JP = J`, `P² = I` and `J² = 2mJ`;
- the binomial theorem gives `T^n = (−P)^n + ((2m−1)^n − (−1)^n) J/(2m)`.

Cyclically reduced words of length `L` are closed walks of length `L` for `T`. Since
`tr P = 0`, `C_L = tr T^L`, which equals `(2m−1)^L + 1` for `L` odd and
`(2m−1)^L + 2m − 1` for `L` even. In every case `C_L <= 2(2m−1)^L`.

## Step 1: a window of positive probability

Fix a letter `x`. The words with `w_1 = w_3 = x` number `(T²)_(xx) (T^(L−2))_(xx)`:
- `(T²)_(xx) = 2m − 1`, counting the choices `w_2 ≠ x^{-1}`;
- `(T^(L−2))_(xx) >= ((2m−1)^(L−2) − 1)/(2m)`, because `P_(xx) = 0` and `I_(xx) = 1`;
- `(2m−1)^(L−2) − 1 >= (2m−2)(2m−1)^(L−3)` for `L >= 3`.

For a uniform cyclically reduced word `w`, this gives

```text
P[w_1 = w_3 = x] >= (2m−1)(2m−2)(2m−1)^(L−3) / (2m · 2(2m−1)^L) = (m−1)/(2m(2m−1)^2).   (W)
```

## Step 2: one relator

The only constraints on `w_2` are with its neighbours. So, given all other letters,
`w_2` is uniform on `A ∖ {w_1^{-1}, w_3^{-1}}`.

Suppose `φ(s) ≠ φ(t)` for letters `s ≠ t`. Choose `x` with `x^{-1} ∉ {s, t}`, which is
possible because `2m >= 4`, and let `E = {w_1 = w_3 = x}`.
- On `E` the admissible set is `A ∖ {x^{-1}}`, of size `2m − 1`, and it contains `s`
  and `t`.
- Write `c = φ(w_1)^{-1} φ(w_3 ⋯ w_L)^{-1}`, which depends only on the other letters.
  Then `φ(w) = 1` iff `φ(w_2) = c`.
- At most one of `s, t` has `φ`-value `c`, so on `E`,
  `P[φ(w) = 1 | other letters] <= (2m−2)/(2m−1)`.

By (W), `P[φ(w) = 1] <= 1 − P[E]/(2m−1) <= 1 − κ_m`.

If `φ` is constant on `A` with value `y`, then `y = φ(a_1^{-1}) = y^{-1}`. So `y² = 1`,
and `φ` is trivial or sends every reduced word of length `ℓ` to `y^ℓ`, the parity map.

## Step 3: all relators

Let `T_φ` be the set of cyclically reduced words of length `L` in `ker φ`, so
`|T_φ| <= (1 − κ_m) C_L`.
- **Independent choices:** `P[R ⊆ ker φ] = (|T_φ|/C_L)^k`.
- **Uniform `k`-subset:** `P[R ⊆ ker φ] = C(|T_φ|, k)/C(C_L, k) = ∏_(i<k) (|T_φ| − i)/(C_L − i) <= (|T_φ|/C_L)^k`.

This proves part 1.

## Step 4: union bounds

**Part 2.** For a finite simple `S`, the normal subgroups `N` of `F_m` with `F_m/N ≅ S`
number `#Epi(F_m, S)/|Aut S| <= |S|^m`. By the import there are at most two types per
order. Apart from the parity kernel, every such `N` has non-constant letters, so
part 1 applies. The expectation is at most
`Σ_(n=2..M) 2 n^m (1−κ_m)^k <= 2 M^(m+1) (1−κ_m)^k`.

**Part 3.** Let `Q` be a nontrivial finite quotient of `Λ` with `|Q| <= M`, and `S`
the quotient of `Q` by a maximal normal subgroup. The kernel of `F_m ->> S` contains
`R`. It is not the parity kernel, because that kernel contains no word of odd length.
Markov's inequality and part 2 give the bound.

Without the import, count every kernel of `F_m ->> Q` by index:
- a subgroup of index `n` gives `(n−1)!` distinct homomorphisms `F_m -> Sym(n)` with
  it as the stabiliser of `1`, so there are at most `(n!)^m/(n−1)! = n (n!)^(m−1)`
  subgroups of index `n`;
- summing over `2 <= n <= M` gives at most `M^((m−1)M + 2)`.

**Part 4.** Since `(1−κ_m)^k <= e^(−κ_m k)` and `(m+1) log M_L <= κ_m k/2`, the bound
of part 3 is at most `2 exp(−κ_m k/2)`, which tends to 0.

Now take `d ∈ (1/3, 1/2)` and restrict to odd multiples of 3.
`density-random-group-hyperbolic-kazhdan-with-positive-b2` holds with probability
tending to 1 along multiples of 3, with the same `k` and the uniform-set model, so it
still holds along this subsequence. The intersection of two events of probability
tending to 1 has probability tending to 1.

## Exact checks (MSI, 2026-09-13)

`experiments/hyperbolic-rf/density_quotient_checks.py`, run with exact arithmetic,
verified:
- `C_L` for `m = 2`, `L <= 11` and `m = 3`, `L <= 7`;
- the formula for `T^n`;
- (W) at the same sizes;
- `P[φ(w) = 1] <= 1 − κ_m` for every non-constant homomorphism `F_2 -> S_3`
  (`L = 3..7`) and `F_2 -> S_4` (`L = 5..7`), for all of `F_3 -> S_3` (`L = 5`), and for
  150 random `F_2 -> A_5` (`L = 7`).

Output: `experiments/hyperbolic-rf/density_quotient_checks.json`.
