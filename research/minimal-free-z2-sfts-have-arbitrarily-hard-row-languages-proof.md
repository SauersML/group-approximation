---
rg: 2
id: minimal-free-z2-sfts-have-arbitrarily-hard-row-languages-proof
kind: route
title: Diagonalize a slope digit set, code it as a Sturmian angle, lift by Durand--Romashchenko, and read freeness off the column projection
target: minimal-free-z2-sfts-have-arbitrarily-hard-row-languages
requires:
  - durand-romashchenko-minimal-sft-simulation
  - continuum-many-infinite-minimal-binary-subshifts
  - sturmian-language-is-turing-equivalent-to-angle
---

Fix recursive `R`. Replacing `R(n)` by `max(n, max_(k<=n) R(k))` only enlarges
`F(R)`, so assume `R` is non-decreasing and `R(n) >= n`. Machines are multitape
Turing machines; all bounds below are recursive in `n` and non-decreasing.

Define the recursive non-decreasing functions

- `R_1(n) = 2^(n^2) * R(n^2)` (bound for Sturmian languages),
- `R_2(m) = 2^(16^m) * R_1(16^m)` (bound for the digit set).

## Step 1. A hard digit set

**Lemma 1.** There is a decidable `D ⊆ {1, 2, 3, ...}` with `D ∉ F(R_2)`, the
input `m` written in unary.

*Proof.* Fix a recursive enumeration `e -> M_e` of Turing machines in which
every machine occurs for infinitely many `e`. Put `m ∈ D` iff `m >= 1` and
`M_m`, run on the unary input `m` for `m*R_2(m*m) + m*m + m` steps, does **not**
halt with output `1`. This is decidable because `R_2` is recursive. Suppose
some `M` decides `D` within `C*R_2(C*m) + C*m + C`. Pick `e >= max(C, 1)` with
`M_e = M`. Since `e >= C`, `e*e >= C*e` and `R_2` is non-decreasing, `M_e`
halts on `e` within the clock, with the correct answer. If it outputs `1`, then
`e ∉ D` by definition, so the answer is wrong. Otherwise `e ∈ D`, and again the
answer is wrong. `∎`

Every eventually periodic subset of `N` is decidable in linear time, hence lies
in `F(R_2)`. So `D` is not eventually periodic, in particular infinite.

## Step 2. The Sturmian angle

Put `α = Σ_(m ∈ D) 4^(-m)`, so `0 < α <= 1/3`.

- **`α` is irrational.** Its base-4 digits are `1` at `m ∈ D` and `0`
  elsewhere, with no tail of `3`s, so this is the base-4 expansion of `α`. It is
  not eventually periodic, so `α` is irrational.
- **`α` is computable.** `D` is decidable and the tail after digit `m` is at
  most `4^(-m)/3`.

Let `A = X_α ⊆ {0,1}^Z` be the Sturmian subshift of
`continuum-many-infinite-minimal-binary-subshifts`. That node gives: `A` is an
infinite minimal subshift.

- **`A` is aperiodic.** If `x ∈ A` had period `p >= 1`, its orbit would be a
  finite nonempty closed invariant set, hence all of `A` by minimality, and `A`
  would be finite.
- **`A` is effective.** By `sturmian-language-is-turing-equivalent-to-angle`,
  `L(A)` is computable from `α`, hence decidable. Its complement is a
  computably enumerable set of forbidden words defining `A`.

## Step 3. The Sturmian language is not in `F(R_1)`

**Lemma 2.** `L(A) ∉ F(R_1)` (input size: word length).

*Proof.* Suppose `L(A)` is decided within `C*R_1(C*n) + C*n + C`. Decide `D` on
unary input `m` as follows. For `k = 1, ..., m`, with `n_k = 6*4^k`:

1. Enumerate `w ∈ {0,1}^(n_k)` and query `L(A)` until a legal `w` is found. One
   exists because `A` is nonempty.
2. Let `c` be the number of `1`s in `w`. By
   `sturmian-language-is-turing-equivalent-to-angle`, `c ∈ {⌊n_k α⌋, ⌊n_k α⌋ + 1}`.
   Since `n_k α` is irrational, `|c/n_k - α| < 1/n_k = 4^(-k)/6`.
3. With `S_(k-1) = Σ_(j ∈ D, j < k) 4^(-j)` known from earlier rounds, declare
   `k ∈ D` iff `c/n_k - S_(k-1) >= 4^(-k)/2`.

Correctness: `α - S_(k-1) = [k ∈ D] 4^(-k) + t` with `0 <= t <= 4^(-k)/3`. If
`k ∈ D`, the estimate exceeds `4^(-k) - 4^(-k)/6 > 4^(-k)/2`. If `k ∉ D`, it is
below `4^(-k)/3 + 4^(-k)/6 = 4^(-k)/2`.

Time: round `k` costs at most `2^(n_k) (C R_1(C n_k) + C' n_k + C')` plus
`poly(4^k)` for the rational arithmetic, for a constant `C'` depending only on
the model. The total is at most
`m * 2^(n_m) (C R_1(C n_m) + C' n_m + C') + poly(4^m)`. For `m` beyond a bound
depending on `C, C'`:
- `C n_m = 6C*4^m <= 16^m`;
- `R_1(16^m) >= 16^m >= n_m`;
- `m * 2^(n_m) (C + 2C') <= 2^(16^m) / 2` and `poly(4^m) <= R_2(m)/2`.

So the total is at most `R_2(m)`. Finitely many smaller `m` are handled by a
table. Hence `D ∈ F(R_2)`, contradicting Lemma 1. `∎`

## Step 4. Lift to a minimal SFT and transfer the bound

By `durand-romashchenko-minimal-sft-simulation`, Theorem 7(a) with `d = 1`,
there are a minimal SFT `B ⊆ Σ_B^(Z^2)` and `π : Σ_B -> {0,1}` with:
- `π(f(i, j))` independent of `j`;
- the column projection `x_f(i) = π(f(i, 0))` lies in `A` for every `f ∈ B`;
- every `x ∈ A` equals some `x_f`.

In particular `B` is nonempty. Put `X = B`.

**Lemma 3.** `w ∈ L(A)` iff some `r ∈ L_row(B)` has `π(r) = w` letterwise.

*Proof.* If `r` sits at `[0,n) × {0}` in `f ∈ B`, then `w = π(r)` sits at
`[0,n)` in `x_f ∈ A`. Conversely, let `w` sit at `[s, s+n)` in `x ∈ A`, and let
`x = x_f`. The horizontal translate of `f` by `s` lies in `B`, and its row
`[0,n) × {0}` projects to `w`. `∎`

**Clause 3.** Suppose `L_row(B)` is decided within `C*R(C*n) + C*n + C`. Then
`w ∈ {0,1}^n` is decided by trying the at most `|Σ_B|^n` words `r` with
`π(r) = w`. This costs at most `|Σ_B|^n (C R(C n) + C' n + C')`. Now use
`R(n) >= n`, the monotonicity of `R`, and `C n <= n^2` for `n >= C`. For `n`
beyond a bound depending on `C, C', |Σ_B|` this is at most
`|Σ_B|^n (C + 2C') R(n^2) <= 2^(n^2) R(n^2) = R_1(n)`. A table covers smaller
`n`. So `L(A) ∈ F(R_1)`, contradicting Lemma 2. Hence `L_row(X) ∉ F(R)`.

**Clause 1.** `B` is minimal by Theorem 7(a).

## Step 5. Freeness

Theorem 7 says nothing about periods, so freeness is derived from the column
projection. Let `B` be defined by a finite forbidden set whose patterns all fit
in an `s × s` square. Suppose `f ∈ B` and `f(v + c) = f(v)` for all `v ∈ Z^2`,
with `c = (c_1, c_2) != 0`.

**Case `c_1 != 0`.** Then
`x_f(i + c_1) = π(f(i + c_1, c_2)) = π(f(i, 0)) = x_f(i)`, using column
constancy of `π`. So `x_f ∈ A` is periodic, contradicting aperiodicity of `A`.

**Case `c_1 = 0`, `c_2 = j != 0`.** Take `j > 0`. For `i ∈ Z` let
`y(i) ∈ Σ_B^j` be the column `(f(i, 0), ..., f(i, j-1))`, so `f` is the
vertically `j`-periodic extension `F_y(i, t) = y(i)(t mod j)`.

1. Every `s × s` window of `F_y` lies in `s` consecutive columns and depends
   only on the word `y[i, i+s)`.
2. Among the positions `0, s, 2s, ...`, two carry the same word of length `s`,
   by pigeonhole: say `y[a, a+s) = y[b, b+s)` with `b - a >= s`.
3. Let `y*` be the `(b-a)`-periodic sequence with `y* = y` on `[a, b)`. Take a
   window `y*[i, i+s)` and its translate `y*[k, k+s)` with `k ∈ [a, b)`,
   `k ≡ i mod (b - a)`. A position `p ∈ [k, k+s)` has `p < b + s`.
   - If `p < b`, then `y*(p) = y(p)`.
   - If `p >= b`, then `p - (b - a) ∈ [a, a+s)`, so
     `y*(p) = y(p - (b-a)) = y(p)`, because `y[a,a+s) = y[b,b+s)`.

   So every length-`s` window of `y*` is a window of `y`.
4. By 1 and 3, every `s × s` window of `F_(y*)` is a window of `F_y = f`. So
   `F_(y*)` avoids the forbidden set, and `F_(y*) ∈ B`.
5. `F_(y*)` has period `(b - a, 0)` with `b - a != 0`. This is the first case,
   a contradiction.

So no configuration of `B` has a nonzero period: `Z^2` acts freely on `X = B`.
**Clause 2** holds, and the theorem is proved. `∎`

## Notes

- The construction is uniform: `R -> D -> α -> B` is effective given an index
  for `R` and an effective version of Theorem 7(a). The theorem only asserts
  existence, which is all the target needs.
- For `d >= 2` the same projection argument gives freeness only for periods
  with a nonzero horizontal part; the vertical case needs a lower-dimensional
  periodic point, which is where `d = 1` is used.
