---
rg: 2
id: thompson-f-induced-chain-avoidance-is-boundary-escape-proof
kind: route
title: Minimality of F on the interval plus returns to a compact set force entry into every open interval, and a last-exit count converts boundary escape back into avoidance
target: thompson-f-induced-chain-avoidance-is-boundary-escape
requires: [thompson-f-dyadic-orbit-walks-are-transient]
---

Notation is as in the target. Only part 3 of Theorem 1, and the direction "escape ⇒ avoidance" of part 4, use the
prerequisite `thompson-f-dyadic-orbit-walks-are-transient`. It applies to every `µ` with `sgr supp µ = F`, with no
further condition.

**Standard imports.**

- (I1) Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*, Enseign. Math. 42 (1996), Lemma 4.2.
  If `[a,b]` and `[c,d]` are subintervals of `[0,1]` with endpoints in `Z[1/2]`, there is a PL homeomorphism
  `[a,b] → [c,d]` whose finitely many breakpoints lie in `Z[1/2]` and whose slopes are powers of 2.
- (I2) The strong Markov property of a Markov chain at stopping times.
- (I3) The Hewitt–Savage 0–1 law. An event that depends on an i.i.d. sequence and is invariant under finite
  permutations of it has probability 0 or 1.
- (I4) The weak law of large numbers, and the central limit theorem for bounded i.i.d. real increments.

**Convention.** Whether the product of `F` is written as composition or reversed composition, the set of all finite
compositions `s_n ∘ ⋯ ∘ s_1` with `s_i ∈ supp µ` is `sgr supp µ`. The same remark is made in
`thompson-f-dyadic-orbit-walks-are-transient`. So under `sgr supp µ = F`, every `g ∈ F` is the composition
`h_n ∘ ⋯ ∘ h_1` for some `n` and some letters with `Π µ(h_i) > 0`.

## Step 1. Uniform hitting from a compact set

**Lemma 1.** Let `K ⊂ (0,1)` be compact and let `J ⊂ (0,1)` be a nonempty open interval. Then there are `N ≥ 1` and
`c > 0` such that `P_t(Z_n ∈ J for some 1 ≤ n ≤ N) ≥ c` for every `t ∈ K`.

*Proof.* Fix dyadic `c' < d'` with `[c',d'] ⊂ J`.

For `t ∈ K`, choose dyadic `a < t < b` in `(0,1)`. By (I1), applied three times, there are PL maps
`[0,a] → [0,c']`, `[a,b] → [c',d']` and `[b,1] → [d',1]` with dyadic breakpoints and power-of-2 slopes. They glue to
an element `g_t ∈ F` with `g_t((a,b)) = (c',d') ⊂ J`.

By the convention, `g_t = s_{n} ∘ ⋯ ∘ s_1` with `s_i ∈ supp µ` and `p_t = Π µ(s_i) > 0`. On the event
`{h_1 = s_1, …, h_{n} = s_{n}}`, which has probability `p_t`, every start `t' ∈ (a,b)` gives
`Z_{n} = g_t(t') ∈ J`.

The open intervals `(a,b) ∋ t` cover `K`. Take a finite subcover indexed by `t_1, …, t_m`. Then
`N = max n_{t_i}` and `c = min p_{t_i}` work. ∎

## Step 2. The alternative (Theorem 1.1)

Fix `t` and `J`. For `j ≥ 3` put `K_j = [1/j, 1 − 1/j]` and `R_j = {Z_k ∈ K_j for infinitely many k}`. Then
`Esc^c = {limsup d(Z_k) > 0} = ∪_j R_j`. It is therefore enough to show that for each `j` and each `M ≥ 0`,
`P_t(R_j ∩ {Z_k ∉ J for all k > M}) = 0`.

Fix `j` and `M`, and let `N` and `c` be as in Lemma 1 for `K_j` and `J`. Define stopping times:

- `T_1 = min{k ≥ M : Z_k ∈ K_j}`;
- `T_{i+1} = min{k ≥ T_i + N : Z_k ∈ K_j}`,

with `min ∅ = ∞`. On `R_j`, all `T_i` are finite.

Let `A_i = {Z_k ∉ J for T_i < k ≤ T_i + N}`. The event `A_i ∩ {T_i < ∞}` is determined by time
`T_i + N ≤ T_{i+1}`. By (I2) and Lemma 1,

`P(A_1 ∩ ⋯ ∩ A_r ∩ {T_r < ∞}) = E[1_{A_1 ∩ ⋯ ∩ A_{r−1} ∩ {T_r < ∞}} P_{Z_{T_r}}(Z_n ∉ J, 1 ≤ n ≤ N)]`
`≤ (1 − c) P(A_1 ∩ ⋯ ∩ A_{r−1} ∩ {T_{r−1} < ∞})`.

By induction this is at most `(1 − c)^r`.

Now `R_j ∩ {Z_k ∉ J for all k > M}` is contained in `A_1 ∩ ⋯ ∩ A_r ∩ {T_r < ∞}` for every `r`. So its probability
is `0`. Take the union over `j ≥ 3` and `M ≥ 0`. ∎

**Part 2 of Theorem 1.** Apply Step 2 with `t = x` and `J = (x,y)`. Almost surely on `Esc^c`, the chain enters
`(x,y) ⊂ [x,y]` at some time `k ≥ 1`. So `θ_{[x,y]} = P_x(avoid [x,y], Esc) ≤ P_x(Esc)`. ∎

## Step 3. Escape gives avoidance (Theorem 1.3 and 1.4)

Fix `x ∈ D`. Let `Av_y = {Z_k ∉ [x,y] for all k ≥ 1}` for dyadic `y > x`. By Step 2, `θ_{[x,y]} = P_x(Av_y ∩ Esc)`.
As `y ↓ x` the events `Av_y` increase. Put `Nr = {Z_k ≠ x for all k ≥ 1}`.

**Claim.** `∪_y Av_y ∩ Esc = Nr ∩ Esc`.

- `⊂`: avoiding `[x,y]` forbids the value `x`.
- `⊃`: on `Esc` there is `L` with `d(Z_k) < d(x)/2` for all `k > L`. The values `Z_1, …, Z_L` are finitely many and,
  on `Nr`, all differ from `x`. Choose dyadic `y > x` with `d ≥ d(x)/2` on `[x,y]` and with `y` below every `Z_k > x`
  for `k ≤ L`. Then `Z_k ∉ [x,y]` for all `k ≥ 1`.

So `lim_{y↓x} θ_{[x,y]} = P_x(Nr ∩ Esc)` by monotone convergence.

Let `σ = min{k ≥ 1 : Z_k = x}`, so `r_x = P_x(σ < ∞)`. The event `Esc` is shift-invariant. By (I2) at `σ`,
`P_x(Esc ∩ {σ < ∞}) = r_x P_x(Esc)`. Hence

`P_x(Nr ∩ Esc) = P_x(Esc) − P_x(Esc ∩ {σ < ∞}) = (1 − r_x) P_x(Esc)`.

The chain started in `D` stays in `D`. It is irreducible there, because `F` is transitive on `D` (by (I1)) and every
element is a positive word. It is transient by `thompson-f-dyadic-orbit-walks-are-transient`. So `r_x < 1`. This
proves Theorem 1.3.

**Theorem 1.4.** The first item implies the second by Theorem 1.2. The second implies the first by Theorem 1.3:
if `P_x(Esc) > 0`, then `θ_{[x,y]} > 0` for all dyadic `y` close enough to `x`.

The second and third items are equivalent by harmonicity. The function `u(t) = P_t(Esc)` satisfies
`u(t) = Σ_h µ(h) u(h t)`, since `Esc` is shift-invariant. Iterating gives `u(z') ≥ P_{z'}(Z_n = z) u(z)`. Choose
`g ∈ F` with `g(z') = z`, written as a positive word of length `n`. Then `P_{z'}(Z_n = z) > 0`, so `u(z) > 0`
implies `u(z') > 0`. ∎

## Step 4. Germ-recurrent walks never escape (Theorem 2)

Let `r` and `A` be as in Theorem 2. Put `a(h) = log2 h'(0)` and `b(h) = log2 h'(1)`, both integers of absolute value
at most `A`. Put `δ = min(r, 2^{-A-1})`.

**No side switching.** Take `Z_k < δ`. Then `Z_k < r`, so `Z_{k+1} = 2^{a(h_{k+1})} Z_k ≤ 2^A δ < 1/2`. Symmetrically,
if `1 − Z_k < δ`, then `Z_{k+1} > 1/2`.

On `Esc` there is `L` with `d(Z_k) < δ` for all `k ≥ L`. By induction the chain then stays on the side of `Z_L` for
all `k ≥ L`. Hence `Esc = ∪_L (E_L^0 ∪ E_L^1)`, where

- `E_L^0 = {Z_k < δ for all k ≥ L}`, and
- `E_L^1 = {1 − Z_k < δ for all k ≥ L}`.

**Exact germ walk.** On `E_L^0`, linearity on `[0,r]` gives, for `k ≥ L`,

`log2 Z_k = log2 Z_L + S_k^{(L)}`, where `S_k^{(L)} = Σ_{i=L+1}^{k} a(h_i)`.

Since `Z_k → 0` on `E_L^0`, this forces `S_k^{(L)} → −∞`.

**The germ walk does not drift to `−∞`.** The increments `a(h_i)`, `i > L`, are i.i.d. and bounded, with mean
`χ_0 ≥ 0`. Put `W_n = S_{L+n}^{(L)}`. There are three cases.

- If `χ_0 > 0`, then `P(W_n ≥ 0) → 1` by the weak law of large numbers.
- If `χ_0 = 0` and `a` is not almost surely `0`, then `P(W_n ≥ 0) → 1/2` by the central limit theorem.
- If `a = 0` almost surely, then `W_n ≡ 0`.

In every case `limsup_n P(W_n ≥ 0) ≥ 1/2`. By Fatou's lemma applied to indicators,
`P(W_n ≥ 0 for infinitely many n) ≥ 1/2`. So `P(W_n → −∞) ≤ 1/2`.

The event `{W_n → −∞}` is invariant under finite permutations of the increments. By (I3) its probability is 0.
Hence `P_t(E_L^0) = 0`.

The same argument with `b` and `1 − Z_k` gives `P_t(E_L^1) = 0`: near 1, `1 − h(s) = h'(1)(1 − s)`. Take the union
over `L`: `P_t(Esc) = 0`.

The remaining conclusions of Theorem 2 follow from Theorem 1.1 and 1.2.

**Symmetric case.** Suppose `µ` is symmetric, meaning `µ(h) = µ(h^{-1})`. Since `a(h^{-1}) = −a(h)` and
`b(h^{-1}) = −b(h)`, the drifts are `χ_0 = χ_1 = 0`. For finitely supported `µ`, take `r` below every breakpoint
distance from the endpoints of the finitely many support elements, and take `A` to be the maximal germ exponent. ∎

## Step 5. Corollary 3

**Simple random walk.** Let `µ` be uniform on `S = {x0^{±1}, x1^{±1}}`. Then `S` is a symmetric generating set, so
`sgr supp µ = F`, and `H(µ) = log 4`. The measure is symmetric and finitely supported, so Theorem 2 gives
`θ_{[x,y]} = 0` for every `x < y`. Prerequisite (B), quantified over all finite-entropy generating `µ`, is false.

**Germ data of `S`.** We use the standard `x0`:

- `t/2` on `[0,1/2]`;
- `t − 1/4` on `[1/2,3/4]`;
- `2t − 1` on `[3/4,1]`.

Let `x1` be the identity on `[0,1/2]` and a copy of `x0` on `[1/2,1]`. Then

- `x0` is linear on `[0,1/2]` and on `[3/4,1]`;
- `x0^{-1}` is linear on `[0,1/4]` and on `[1/2,1]`;
- `x1` is linear on `[0,1/2]` and on `[7/8,1]`;
- `x1^{-1}` is linear on `[0,1/2]` and on `[3/4,1]`.

All germ exponents lie in `{−1, 0, 1}`. So Theorem 2 holds with `r = 1/8` and `A = 1`.

**Infinite-breakpoint symmetric example.** Fix `N ≥ 1`. Choose `4^N` dyadic intervals with pairwise disjoint
interiors inside `[1/4,3/4]`. On each, place a copy of `x0` rescaled by (I1). Each copy is the identity outside its
interval and has at least 2 breakpoints. Let `k_N` be their product. The factors commute, `k_N` is supported in
`[1/4,3/4]`, and `|Br(k_N)| = |Br(k_N^{-1})| ≥ 2·4^N`.

Put `w_N = c 2^{-N}/N²`, with `c` chosen so that `Σ w_N = 1`, and

`µ = ½ · Unif(S) + ½ Σ_N w_N (δ_{k_N} + δ_{k_N^{-1}})/2`.

- **Symmetric and generating:** `S ⊂ supp µ`.
- **Finite entropy:** `H(µ) ≤ log 8 + ½ Σ_N w_N (log2(1/w_N) + 1) log 2 < ∞`, since `log2(1/w_N) = N + 2 log2 N + O(1)`.
- **Infinite breakpoint moment:** `E_µ|Br(h)| ≥ ½ Σ_N w_N · 2·4^N = c Σ_N 2^N/N² = ∞`.
- **Theorem 2 applies:** every `k_N^{±1}` is the identity on `[0,1/4] ∪ [3/4,1]`. So it is linear on `[0,1/8]` and on
  `[7/8,1]`, with germ exponents `0`. Together with the data for `S`, Theorem 2 holds with `r = 1/8` and `A = 1`.

Hence `θ_{[x,y]} = 0` for every interval. ∎

**Internal avoidance quantities.** The proof of `thompson-f-interval-avoiding-walks-have-positive-entropy` works
with three auxiliary measures, all defined there:

- `λ = (µ+δ_e)/2`;
- `µ1 = λ^{*k}`;
- `ν`, which is `µ1` conditioned on `F ∖ Δ`, where `Δ = {e, b}` (its Step 4).

It lower-bounds `θ_ν` by `θ/2`. If one tried to assume `θ_ν > 0` directly, the kill still applies whenever `µ` is in
the class of Theorem 2 and `supp µ ∖ {b}` generates `F`, for the following reasons.

- **Linearity and germ bounds.** A composition of `k` elements that are linear on `[0,r]` with germ exponents at most
  `A` is linear on `[0, r 2^{-kA}]` with exponent at most `kA`. The same holds at `1`. So `λ^{*k}` satisfies the
  first hypothesis of Theorem 2, and so does `ν`, because `supp ν ⊂ supp λ^{*k}`.
- **Drifts.** Germ exponents add under composition, so the drifts of `λ^{*k}` are `kχ_0/2 ≥ 0` and `kχ_1/2 ≥ 0`. The
  letters `e` and `b` have germ exponent `0` at both ends, because `supp b ⊂ [x,y] ⊂ (0,1)`. So conditioning them away
  multiplies the drifts by the positive factor `1/(1 − µ1(Δ))`.
- **Generation.** `supp ν ⊇ supp λ^{*k} ∖ Δ ⊇ supp µ ∖ {b}` (pad a letter with `k−1` lazy steps). This generates `F`
  by assumption.

So Theorem 2 gives `θ_ν = 0`.

For the simple random walk this holds for every admissible `b` and `k`. Every such `b` is supported in `[x,y] ⊂ (0,1)`,
while `x0^{±1}` and `x1^{±1}` move points arbitrarily close to `1`. So `b ∉ S` and `supp ν ⊇ S`.

Two further variants also fail.

- **The lazy chain.** It visits the same positions as the `µ`-chain, with repetitions inserted.
- **Eventual avoidance** ("avoid `[x,y]` from some time on"). By Theorem 1.1 this has probability `0` on `Esc^c`.
