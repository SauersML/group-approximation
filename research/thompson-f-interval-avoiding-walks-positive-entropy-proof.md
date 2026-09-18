---
rg: 2
id: thompson-f-interval-avoiding-walks-positive-entropy-proof
kind: route
title: Conjugated bump insertions are readable at an uncovered support endpoint, so avoidance of the support interval gives linear conditional entropy
target: thompson-f-interval-avoiding-walks-have-positive-entropy
requires: [thompson-f-dyadic-orbit-walks-are-transient]
---

The theorem uses no prerequisite beyond the import below. The corollary also uses
`thompson-f-dyadic-orbit-walks-are-transient`.

**Import (entropy criterion).** A. Erschler and J. Frisch, *Poisson boundary of group extensions*,
arXiv:2206.11111v3, §2, Theorem 2.3, verbatim:

> Theorem 2.3 (Entropy criterion, [13, 32, 33]). Let µ be a probability measure on a group G. If the measure µ has
> finite entropy, then the Poisson boundary of the random walk (G, µ) is trivial if and only if the entropy of the
> random walk is 0.

Here [13, 32, 33] are Derriennic and Kaimanovich–Vershik. The entropy of the random walk is
`h(µ) = lim_n H(µ^{*n})/n`. The limit exists by subadditivity.

The only other tools are elementary Shannon inequalities: conditioning does not increase entropy, the chain rule,
and `I(S;π) ≤ H(π)`.

**Step 0 (conventions).** For `g ∈ F` and `t ∈ (0,1)` put `β(g)(t) = log2 g'(t+) − log2 g'(t−) ∈ Z`. The chain rule
for increasing maps gives `β(gh)(t) = β(h)(t) + β(g)(h t)`. Three facts follow:

- (a) If `g` fixes `t`, then `β(g^S)(t) = S β(g)(t)` for `S ≥ 0`.
- (b) If `Pz = t` and `g` fixes `z`, then `β(PgP^{-1})(t) = β(g)(z)`. Expand `β(P g P^{-1})(t)` by the cocycle. The
  outer terms `β(P^{-1})(t) + β(P)(z)` add up to `β(P^{-1}P)(z) = 0`.
- (c) If `g` is the identity on a neighbourhood of `t`, then `β(g)(t) = 0`.

Let `b` and `[x,y]` be as in the theorem. Since `b` is the identity to the left of `x` and not the identity on any
right neighbourhood of `x`, it has the form `t ↦ x + 2^s(t − x)` just right of `x` with `s ≠ 0`. So `b` fixes `x` and
`s := β(b)(x) ≠ 0`.

**Step 1 (the measure `µ1`).** Let `λ = (µ+δ_e)/2`. Then `H(λ) ≤ H(µ) + log 2 < ∞`, and `λ` has the same bounded
harmonic functions as `µ`: `u = ½u + ½ Σ µ(h)u(·h)` if and only if `u = Σ µ(h)u(·h)`. Choose `k` with
`b ∈ supp µ^{*k}`, and put `µ1 = λ^{*k}`. Then `µ1(e) ≥ 2^{-k}` and `µ1(b) ≥ 2^{-k} µ^{*k}(b) > 0`. Also
`H(µ1) < ∞` and `h(µ1) = k h(λ)`.

Put `Δ = {e, b}`, `p = µ1(Δ)` and `q = µ1(b)/p ∈ (0,1)`. Then `p < 1`: otherwise every `µ`-step lies in `{e,b}`,
the chain from `x` stays at `x`, and `θ = 0`. Let `ν` be `µ1` conditioned on `F ∖ Δ`.

**Step 2 (conditioning on the non-`Δ` letters).** Let `Y_1, …, Y_n` be i.i.d. of law `µ1` and `X_n = Y_1 ⋯ Y_n`, so
`H(X_n) = H(µ1^{*n})`. Put `V_t = Y_t` if `Y_t ∉ Δ` and `V_t = ⋆` otherwise, and `V = (V_1,…,V_n)`. Then
`H(X_n) ≥ H(X_n | V)`. (This is the `Δ`-restriction entropy of Erschler–Frisch, Definition 4.9; only the trivial
inequality is used.)

Given `V`, the positions of the `Δ`-letters are known. The `Δ`-letters are i.i.d., equal to `b` with probability `q`
and to `e` otherwise. Group the maximal runs of consecutive `Δ`-positions and let `m` be their number. Then

`X_n = W_1 b^{S_1} W_2 b^{S_2} ⋯ W_m b^{S_m} W_{m+1}`.

Here the `W_i` are the products of the non-`Δ` letters between runs, and they are `V`-measurable. `W_1` and
`W_{m+1}` may be empty, while `W_2, …, W_m` are nonempty. Given `V`, the `S_i ~ Bin(r_i, q)` are independent, where
`r_i ≥ 1` is the length of run `i`. Put `P_i = W_1 ⋯ W_i` and `b_i = P_i b P_i^{-1}`. Since
`P_{i−1} b^{S} W_i = b_{i−1}^{S} P_i`, induction gives

`X_n = π P_{m+1}`, with `π = b_1^{S_1} ⋯ b_m^{S_m}` and `P_{m+1}` `V`-measurable.

Put `π_i = b_1^{S_1} ⋯ b_i^{S_i}` and `S = (S_1,…,S_m)`. Everything below is conditional on `V`. Since `π` is a
function of `S`, `H(π) = I(S;π) = H(S) − H(S|π)`. By the chain rule,
`H(S|π) = Σ_i H(S_i | π, S_{i+1}, …, S_m)`. From `π` and `S_{i+1},…,S_m` one computes
`π_i = π (b_{i+1}^{S_{i+1}} ⋯ b_m^{S_m})^{-1}`, so each term is at most `H(S_i | π_i)`. Hence

`H(X_n | V) ≥ E Σ_{i=1}^m [ H(S_i) − H(S_i | π_i) ]`, where every bracket is `≥ 0`.

**Step 3 (the detector).** Put `x_i = P_i x`. Call run `i` *good* (a `V`-measurable event) if
`x_i ∉ P_j[x,y]` for all `1 ≤ j < i`. The element `b_i` is supported in `P_i[x,y]` and fixes its left endpoint
`x_i`. Also `π_{i−1}` is supported in the closed set `∪_{j<i} P_j[x,y]`, so on a good run it is the identity near
`x_i`. By the cocycle identity and facts (a)–(c),

`β(π_i)(x_i) = β(b_i^{S_i})(x_i) + β(π_{i−1})(x_i) = S_i s + 0`.

So on a good run `S_i = β(π_i)(x_i)/s` is a function of `π_i` and `V`, and `H(S_i | π_i) = 0`. Moreover
`H(Bin(r,q)) ≥ H(Bin(1,q)) =: h_q > 0` for `r ≥ 1`, because adding an independent summand does not decrease
entropy. Therefore

`H(X_n | V) ≥ h_q · E #{i ≤ m : run i is good}`.

**Step 4 (good runs have probability at least `θ/2`).** Now average over `V`. Condition only on the `Δ`/non-`Δ`
pattern. The non-`Δ` letters are then i.i.d. of law `ν`. Fix `i ≥ 2`, and let `u_1, …, u_c` be the non-`Δ` letters
of `W_2, …, W_i` in order, so that `P_j^{-1} P_i = W_{j+1} ⋯ W_i`. The points `W_{j+1} ⋯ W_i (x)` for `1 ≤ j < i` are
among `U_s := u_{c−s+1} ⋯ u_c (x)` for `1 ≤ s ≤ c`. Since `u_c, u_{c−1}, …` are i.i.d. `ν`, `(U_s)` is the induced
chain of `ν` from `x`. Hence `P(run i good | pattern) ≥ θ_ν := P_x(ν-chain never enters [x,y])`. Run `1` is always
good.

Next compare `θ_ν` with `θ`, in three moves.

- *`θ_ν ≥ θ_{µ1}`.* The letters `e` and `b` fix every point of `[0,1] ∖ (x,y)`. On the event that the `µ1`-chain
  from `x` never enters `[x,y]`, deleting its `Δ`-steps leaves the positions unchanged except for repetitions. The
  deleted sequence is i.i.d. `ν`, and its chain also avoids `[x,y]`.
- *`θ_{µ1} ≥ θ_λ`.* The `µ1`-chain has the law of the `λ`-chain observed at times `k, 2k, …`.
- *`θ_λ ≥ θ/2`.* The `λ`-chain avoids `[x,y]` if its first step is not lazy and its non-lazy steps drive a
  `µ`-chain that avoids `[x,y]`. Holding at a point outside `[x,y]` is harmless.

So `θ_ν ≥ θ/2 > 0`. The number of runs satisfies `m ≥ #{2 ≤ t ≤ n : Y_t ∈ Δ, Y_{t−1} ∉ Δ}`, whose mean is
`(n−1)p(1−p)`. Therefore

`H(µ1^{*n}) ≥ H(X_n | V) ≥ h_q (θ/2) p(1−p) (n−1)`.

**Step 5 (conclusion).** Dividing by `n` gives `k h(λ) = h(µ1) ≥ h_q θ p(1−p)/2 > 0`. By the imported criterion
applied to the finite-entropy measure `λ`, the Poisson boundary of `λ` is nontrivial. So there is a nonconstant
bounded `λ`-harmonic function, which by Step 1 is `µ`-harmonic. Hence `µ` is not Liouville. □

For generating `µ`, the copy `b` of `x_0` on `[x,y]` lies in `sgr supp µ = ∪_k supp µ^{*k}`. It is the identity off
`[x,y]` and has slope `2^{±1}` just right of `x`.

**Step 6 (corollary).** Let `H(µ) < ∞`, `sgr supp µ = F`, `µ` Liouville, and fix `x ∈ D`. By the theorem,
`θ_{[x,y]} = 0` for every dyadic `y ∈ (x,1)`. So a.s. the chain from `x` visits `[x,y]` at some time `k ≥ 1`, for all
countably many `y` at once.

- *Positive probability from `x`.* By `thompson-f-dyadic-orbit-walks-are-transient`, `ρ := P_x(Z_k = x for some k ≥ 1)
  < 1`, and every point is visited finitely often. On the event of no return to `x`, the path meets `(x,y]` for
  every `y > x`. So it meets infinitely many distinct points accumulating at `x` from the right, and it does so after
  every time `K`. This is the shift-invariant event `A_x`, and `P_x(A_x) ≥ 1 − ρ > 0`.
- *Zero-one law.* Put `φ(z) = P_z(A_x)`. It is bounded and satisfies `φ(z) = Σ_h µ(h) φ(h z)`. Put
  `u(g) = φ(g^{-1} x)`. Then `u(g) = Σ_h µ(h) u(g h^{-1})`, so `u` is `µ̌`-harmonic.
  - Since `H(µ̌^{*n}) = H(µ^{*n})`, we get `h(µ̌) = h(µ) = 0` (criterion for `µ`), and the criterion for `µ̌` makes
    `u` constant. As `F` is transitive on `D`, `φ ≡ c`.
  - By Lévy's zero-one law, `φ(Z_k) = P(A_x | Z_0, …, Z_k) → 1_{A_x}` a.s. So `c ∈ {0,1}`, and `c ≥ 1 − ρ` forces
    `c = 1`. □

**Where this route stops.** The hypothesis `θ > 0` is not automatic. Transience controls visits to points, not
real-topology accumulation, and nothing excludes an infinitely supported finite-entropy `µ` whose induced chain
wanders densely. The corollary shows this is exactly the case that remains: a finite-entropy Liouville witness has
a transient induced chain whose path a.s. approaches every dyadic from the right.
