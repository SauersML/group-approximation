---
rg: 2
id: set-indexed-repetition-keyed-hosts-proof
kind: route
title: Sort by a public key, then scramble with a shared uniform permutation -- on the event (distinct keys, no cut edge), which lies inside Good, the sorted lists are matched and the scrambled tuple is exactly iid, so the ordered optimum is played at loss Pr[not E] <= n*cut + C(n,2)*collision; Theorem CP (b) at mu = w^n then lets the base SDP decide
target: set-indexed-repetition-obeys-the-base-sdp-bound-on-keyed-hosts
requires:
  - correlated-products-cannot-substitute-rounds-for-alphabet
  - steurer-hellinger-relaxation-rounding
  - sdp-fixed-precision-solvable-gls
  - set-indexed-repetition-escapes-the-base-sdp-bound
---

The notation is that of the target claim. A strategy for a set game may use
shared randomness. Its value is an average over the shared string of the
values of deterministic strategies, so it never exceeds `val`. All
probabilities are over `n` iid edges `e_j = (u_j, v_j, π_j) ~ w`, or over iid
tagged edges `((u_j, a_j), (v_j, b_j), π_j)`, together with the shared string.
None of them is conditioned unless stated otherwise.

## Step 1: Theorem K

Fix a key `κ`. Fix an optimal deterministic strategy of the ordered game
`G^n`: maps `a* : U^n -> [k]^n` and `b* : V^n -> [k]^n` with

```text
Pr[ b*(v_1..v_n)_i = π_i( a*(u_1..u_n)_i )  for all i ]  =  opt(G^n)
```

under iid edges. Fix a total order `<_L` on the left vertices of the game
being played (tagged or not) and `<_R` on the right ones.

**Strategy.** The shared string is a uniform permutation `σ` of `[n]`.

- Alice receives a set `A` of `n` elements. She lists them as `x_1, ..., x_n`,
  sorted by `(κ(underlying vertex), <_L)`. She puts
  `u' := (x_σ(1), ..., x_σ(n))`, drops the tags, computes `a*(u')`, and gives
  `x_σ(i)` the label `a*(u')_i`.
- Bob does the same with his set, sorted by `(κ, <_R)` into `y_1, ..., y_n`,
  using `b*`.

The strategy is tag-blind, and it is well defined on every input set.

**The event `E`.** Let `E` be the event that the keys `κ(u_1), ..., κ(u_n)`
are pairwise distinct and `κ(u_j) = κ(v_j)` for every `j`.

- **(K1) `E ⊂ Good`.** On `E`, distinct keys force distinct `u_j`. The keys
  `κ(v_j) = κ(u_j)` are then also distinct, which forces distinct `v_j`. This
  holds for the underlying vertices, so it also holds for the tagged ones.
- **(K2) Matched sorting on `E`.** Let `τ` be the permutation for which
  `x_i` is the element coming from edge `τ(i)`. Define `τ` by the same sorting
  rule for all edge tuples, ties included, so that it is a function of the
  tuple. On `E` the keys of Bob's elements are the same distinct numbers
  `κ(u_j)`, attached to the same indices. So Bob's `i`-th smallest element
  comes from edge `τ(i)`, that is, `y_i = v_(τ(i))` (with tag).
- **(K3) The simulated tuple.** Put `ρ := τ ∘ σ` and
  `f := (e_(ρ(1)), ..., e_(ρ(n)))`. On `E`, position `i` of Alice's tuple `u'`
  holds the left end of `f_i`, and position `i` of Bob's tuple holds its right
  end. So the players win the set game iff `(a*, b*)` wins the ordered game on
  the tuple `f`.
- **(K4) Exchangeability.** `f` has law exactly `w^(⊗n)`. Indeed:
  - `σ` is uniform and independent of the edge tuple `e`, and `τ = τ(e)` is a
    function of `e`. For each fixed `e`, `σ ↦ τ(e) ∘ σ` is a bijection of
    `S_n`. So `ρ` is uniform and independent of `e`.
  - For each fixed `ρ`, the tuple `e ∘ ρ` has law `w^(⊗n)`, because the
    coordinates of `e` are iid.
  - Mixing over the independent `ρ` gives `f ~ w^(⊗n)`.

  In the tagged case the same argument applies to tagged edges. Since
  `(a*, b*)` ignores tags, the ordered win on `f` has probability `opt(G^n)`.
- **(K5) Conclusion.** Let `W` be the set-game win event and `W_f` the ordered
  win on `f`. By (K1) and (K3), `W ∩ E = W_f ∩ E ⊂ Good`. Therefore
  `Pr[W | Good] >= Pr[W ∩ E]/Pr[Good] >= Pr[W_f ∩ E] >= opt(G^n) - Pr[not E]`.
  By the union bound over `j` and over pairs `i < j`,

  ```text
  Pr[not E]  <=  Σ_j Pr[κ(u_j) ≠ κ(v_j)] + Σ_(i<j) Pr[κ(u_i) = κ(u_j)]  =  n θ(κ) + C(n,2) q_A(κ).
  ```

  Here `Pr[κ(u) = κ(u')] = Σ_r µ_A(κ^(-1)(r))^2` for independent `u, u' ~ µ_A`.

The value of the set game is at least `Pr[W | Good]`, so Theorem K holds. The
tagged and untagged cases differ only in the conditioning event, which (K1)
covers in both. A key drawn from shared randomness gives nothing new: by
averaging, some fixed key does at least as well.

## Step 2: Corollary K

Theorem CP (b) of `correlated-products-cannot-substitute-rounds-for-alphabet`
applies with `µ = w^(⊗n)`, for which `D = 1`, `K = k` and all factors equal
`G`. It gives

```text
opt(G^n)  >=  1 - C_+ sqrt(n ln k (1 - sdp(G))).
```

Substituting this into Theorem K proves Corollary K.

## Step 3: Proposition T

Let `Good_tag` be the conditioning event of `G_{tag,M}^{{n}}` (distinct tagged
left vertices, distinct tagged right vertices). Let `Good_0` be the event that
the underlying `u_j` are distinct and the underlying `v_j` are distinct. Then
`Good_0 ⊂ Good_tag`.

Take an optimal strategy `(α_0, β_0)` of `G^{{n}}`.

- In the tagged game, if the underlying vertices of Alice's set are distinct,
  she drops the tags, answers `α_0` on the underlying set, and copies each
  label back to its tagged element. Otherwise she answers arbitrarily. Bob
  does the same with `β_0`.
- The underlying edge tuple of iid tagged edges is iid `w^(⊗n)`, because the
  tags are independent of the edges.
- On `Good_0`, the tagged win coincides with the win of `(α_0, β_0)` on the
  underlying instance.

Hence

```text
val(G_tag^{{n}})  >=  Pr[win ∩ Good_tag]/Pr[Good_tag]  >=  Pr[win_0 ∩ Good_0]
                  =   val(G^{{n}}) Pr[Good_0]  >=  val(G^{{n}}) - Pr[not Good_0],
```

and the union bound over pairs gives
`Pr[not Good_0] <= C(n,2)(Σ_u µ_A(u)^2 + Σ_v µ_B(v)^2) = c_n(G)`.

## Step 4: Theorem D and Corollary D

Fix `x`. Write `G = G_x`, `n = n_x`, `k = k_x <= K`.

- **YES.** Here `sdp(G) >= opt(G)`, so `n(1 - sdp(G)) <= n(1 - opt(G)) <= η_Σ`.
- **NO.** Soundness and Corollary K (valid for every `M`) give

  ```text
  1 - Γ  >=  val(G_tag^{{n}})  >=  1 - C_+ sqrt(n ln k (1 - sdp(G))) - ζ.
  ```

  So `C_+ sqrt(n ln k (1 - sdp(G))) >= Γ - ζ > C_+ sqrt(1.5 η_Σ ln K)`. Since
  `2 <= k <= K`, this forces `n(1 - sdp(G)) > 1.5 η_Σ`.
- **Algorithm.** `G` has polynomial size, and `n` is given in binary, so
  `η_Σ/(4n)` has polynomially many bits. The basic SDP of `G` is solved to
  additive precision `η_Σ/(4n)` in polynomial time. This uses the solver of
  the proof of Theorem CP (c) (test `T`, item 2, of
  `correlated-products-cannot-substitute-rounds-for-alphabet-proof`), that is,
  `sdp-fixed-precision-solvable-gls` with the ball data recorded there. It
  returns `s~` with `sdp(G) - η_Σ/(4n) <= s~ <= sdp(G)`, in time polynomial
  in `|G|` and `log(4n/η_Σ)`. Accept iff `n(1 - s~) <= 1.25 η_Σ`.
  - YES gives `n(1 - s~) <= η_Σ + η_Σ/4`.
  - NO gives `n(1 - s~) > 1.5 η_Σ - η_Σ/4`.

Nothing about `κ`, `M` or the output game is computed. Corollary D is the
contrapositive. In its UGC form, `Γ = 1 - δ'` and `η_Σ <= 2ε'` give
`(1 - δ' - ζ)^2 <= C_+^2 · 3ε' ln K = 24 C_3 ε' ln K`.

`z_n(G_tag) <= z_n(G)` holds because every key of `G` lifts to a tag-blind
key of `G_tag` with the same `θ` and `q_A`. Tagging leaves `µ_A` of
underlying classes unchanged.

## Step 5: Lemma C (odd cycle)

The host of the w21 node is `C_m`, with `x` uniform in `Z_m` and `y = x + d`,
where `d = 0` with probability `1/2` and `d = ±1` with probability `1/4`.
Every edge has weight `>= 1/(4m)`. The edges `(x, x)` and `(x + 1, x)` form a
Hamiltonian cycle `L_0 R_0 L_1 R_1 ... L_(m-1) R_(m-1) L_0` of length `2m`.

Take a key with `c` nonempty classes.

- **`c = 1`.** Then `θ = 0` and `q_A = 1`, so the cost is `C(n,2) >= n^2/4`
  for `n >= 2`.
- **`c >= 2`.** A cyclic sequence using `c >= 2` distinct colors changes color
  at least `c` times. So at least `c` cycle edges are cut, and
  `θ >= c/(4m)`. At most `c` classes meet `U`, so Cauchy-Schwarz gives
  `q_A >= 1/c`. Hence, by AM-GM,

  ```text
  n θ + C(n,2) q_A  >=  n c/(4m) + C(n,2)/c  >=  2 sqrt(n C(n,2)/(4m))  >=  n^(3/2)/(2 sqrt m),
  ```

  using `C(n,2) >= n^2/4`.

The lower bound `min(n^2/4, n^(3/2)/(2 sqrt m))` is at least `1` once `n >= 2`
and `n^3 >= 4m`.

Disjoint copies: with key = copy index, no edge is cut and each class has
`µ_A`-mass `1/M`. So `q_A = 1/M` and the cost is `C(n,2)/M <= n^2/(2M)`.

## Step 6: Lemma S

Let `κ` attain `z_n(G) <= ζ`, with parts `P_r`. For each part with
`µ_A(P_r) > 0`, put `Φ_r := Pr_e[v ∉ P_r | u ∈ P_r]`. Then

```text
Σ_r µ_A(P_r) Φ_r  =  Pr_e[κ(u) ≠ κ(v)]  =  θ  <=  ζ/n,
Σ_r µ_A(P_r) · µ_A(P_r)  =  q_A  <=  ζ/C(n,2).
```

Both are averages under the probability vector `(µ_A(P_r))_r`. By Markov's
inequality:

- the parts with `Φ_r > 4θ` carry mass `< 1/4`;
- the parts with `µ_A(P_r) > 4 q_A` carry mass `< 1/4`.

The remaining parts carry mass `> 1/2`, and each has `µ_A(P_r) <= 4ζ/C(n,2)`
and `Φ_r <= 4ζ/n`. For the comparison in the claim, with
`δ_0 = 4ζ/C(n,2) = 8ζ/(n(n-1))`, we have
`sqrt(2ζ δ_0) = 4ζ/sqrt(n(n-1)) >= 4ζ/n`.

## Step 7: subcube keys on noisy-cube hosts

The host has left and right vertex set `{0,1}^d`. Its edge law is `u` uniform
and `v = u ⊕ ξ`, with `ξ_i` iid `Bernoulli(η)`. The permutations play no role
in the key cost.

The key "first `t` coordinates" (on both sides) has:

- `θ = 1 - (1-η)^t <= tη`;
- `q_A = 2^(-t)`.

At `n = ε'/η`, taking `t = ⌈2 log2 n⌉ + s` gives, for every integer `s >= 0`,

```text
z_n  <=  ε' (2 log2(ε'/η) + s + 1) + 2^(-s-1).
```

So the host is keyed with `ζ` small against `1 - δ'` whenever
`2 ε' log2(ε'/η)` is small against `1 - δ'`. Table [5] of the check evaluates
`min_t [n t η + C(n,2) 2^(-t)]`.

This is only an upper bound on `z_n`. It is not claimed here that such hosts
are keyless in the complementary regime.
