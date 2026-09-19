---
rg: 2
id: raz-rosen-expander-repetition-rate-is-quartic-in-gap
kind: claim
title: The Raz--Rosen expander repetition bound, as proved, certifies per-round rate at most 2c 10^-40 eps lambda^4/log(2/lambda) for projection games (c Rao's constant) and at most 10^-12 eps^2/16 in general, so both theorems lie in the rate classes that expansion-certified-repetition-caps-deficit-ratio kills
distinct_from:
  akkstv-expansion-parallel-repetition-bound: that is the AKKSTV Feige--Lovasz bound with rate eps lambda/log(1/eps); this is the Raz--Rosen information-theoretic bound, whose proved rate is quartic in the gap, and it covers projection games, not only unique games.
  expansion-certified-repetition-caps-deficit-ratio: that is the class kill and lists "strong repetition on expanders" bounds of rate O(poly(lambda) gamma) as members without checking any; this checks the Raz--Rosen member against the verbatim proof and supplies its constants.
  dinur-steurer-projection-game-repetition-bound: that is a universal quadratic rate independent of expansion; Raz--Rosen use such a rate (Rao's) as their second stage, and gain linearity in eps only by paying lambda^4.
  raz-odd-cycle-repetition-lower-bound: that is a lower bound for one non-expanding game; here it is used only in a remark on a statement-level reading.
---

**ESTABLISHED, BY CITATION PLUS ARITHMETIC.** The verbatim source is in the
route `raz-rosen-expander-projection-repetition-citation`, which quotes ECCC
TR10-142.

**Setting.** A two-prover game `G` is played on a `(X, Y, d_X, d_Y, 1 − λ_RR)`
expander. Questions are uniform over the edges of a biregular bipartite graph.
`1 − λ_RR` is the second singular value of the normalized biadjacency matrix
`M`, and `λ_RR` lies in `(0, 1]`. The walk operator on `X ∪ Y` has spectrum
`{±σ_i}`, together with zeros. Such a game is therefore λ-gapped in the sense
of `expansion-certified-repetition-caps-deficit-ratio` exactly when
`λ_RR >= λ`. `log` is base 2, and `c > 0` is the universal constant in Rao's
theorem, as the source quotes it.

**Theorem.** Let `G` have value at most `1 − ε`, with `0 < ε < 1/2`, and let
`λ = λ_RR`.

1. *(Projection games.)* The proof of Raz--Rosen Theorem 2 gives, for every `n`,

   ```text
   val(G^⊗n)  <=  (1 − ψ_2)^n ,    ψ_2  <=  2c · 10^(−40) · ε λ^4 / log(2/λ)  <=  2c · 10^(−40) · λ ε .
   ```

   So the certified per-round rate is `Θ(ε λ^4/log(2/λ))`. It is linear in
   `ε` and quartic, up to the logarithm, in the gap.
2. *(General games.)* Raz--Rosen Theorem 1, with answer set size `s >= 2`,
   gives `val(G^⊗n) <= (1 − ψ_1)^n` with
   `ψ_1 <= 2ε^2 c_1(λ)/log s <= 10^(−12) ε^2/16`. Here
   `c_1(λ) = (1/32)10^(−12)λ^2/(log(2/λ))^2`.
3. *(Class membership.)* Read on a λ-gapped source with NO deficit `γ`, at
   `γ_0 = min(γ, 1/4)`:
   - Theorem 2 is a `Rate(0, κ_RR)` amplifier with `κ_RR = 2c · 10^(−40)`, and
     the rate is certified uniformly.
   - Theorem 1 is a `Rate(K_RR, 0)` amplifier with `K_RR = 10^(−12)/16`.
   - Item 3 of the kill caps any Theorem 2 amplifier on a hard source, unless
     `P = NP`, at deficit ratio `R <= 3184 κ_RR = 6368 c · 10^(−40)`. Since
     `c <= 6` (proof, step 4), this is below `4 · 10^(−36)`, far under the
     padding line `2`.
   - A Theorem 1 amplifier needs `γ >= sqrt(R*/(2 K_RR)) sqrt(η)` to certify
     ratio `R*`, which is item 4 of the kill. That condition makes the source
     already sqrt-scale.

   Neither theorem meets (P2). This closes the "Unchecked" Raz--Rosen item of
   `sqrt-scale-unique-games-hardness`.

**Proof.**

1. *Two stages.* The proof of Theorem 2 has two stages, quoted in the route.
   Put `ε′ = 10^(−6) ε λ/log(2/λ)` (footnote 5) and
   `m = 10^4 (ε′)^(−1) λ^(−1) = 10^10 log(2/λ)/(ε λ^2)`. Since `ε < 1/2` and
   `λ <= 1`, `m >= 2 · 10^10`.
   - Display (32) gives `val(G^⊗m) <= 1 − 10^(−15) λ`.
   - Rao's theorem is applied to the projection game `G^⊗m`, whose deficit is
     `10^(−15) λ`, played `n/m` times.

   So `val(G^⊗n) <= (1 − a)^(n/m)` with `a = c · 10^(−30) λ^2`. This is the
   quoted `(1 − Ω(λ^2))^(n·10^(−4)(ε′)λ)`, since `n/m = n · 10^(−4) ε′ λ`.
2. *The per-round rate.* Define `ψ_2` by `(1 − ψ_2)^n = (1 − a)^(n/m)`, so
   `ψ_2 = 1 − (1 − a)^(1/m)`. By step 4, `a <= 6 · 10^(−30) <= 1/2`. Then
   `(1 − a)^(1/m) = exp(ln(1 − a)/m) >= 1 + ln(1 − a)/m >= 1 − 2a/m`, so
   `ψ_2 <= 2a/m = 2c · 10^(−40) ε λ^4/log(2/λ)`.
   On `(0, 1]` we have `log(2/λ) >= 1` and `λ^3 <= 1`, which gives
   `ψ_2 <= 2c · 10^(−40) λ ε`. This is item 1.
3. *Theorem 1.* The bound is `(1 − x)^(n/log s)` with
   `x = ε^2 c_1(λ) <= ε^2 (1/32) 10^(−12)`, because `λ <= 1` makes
   `log(2/λ) >= 1`. For `s >= 2`, `1/log s <= 1`. As in step 2,
   `ψ_1 <= 2x <= 10^(−12) ε^2/16`. This is item 2.
4. *Rao's constant.* The constant satisfies `c <= 6`. The odd cycle game `C_3` is
   a unique game, hence a projection game, and has value exactly `5/6`
   (`raz-odd-cycle-repetition-lower-bound`, which checks this exactly). Rao's
   theorem at `n = 1` with `ε = 1/6` gives `5/6 <= 1 − c/36`.
5. *Membership.*
   - A NO instance of a λ-gapped source has `λ_RR >= λ` and deficit at least
     `γ >= γ_0`, with `γ_0 < 1/2`. Theorem 2 applies with `ε = γ_0`, because
     value at most `1 − γ` implies value at most `1 − γ_0`.
   - `λ ↦ λ^4/log(2/λ)` is increasing on `(0, 1]`, so the rate
     `ψ(λ, γ) := 2c · 10^(−40) γ_0 λ^4/log(2/λ)` is certified on every NO
     instance. It is at most `κ_RR λ γ`, which is membership in `Rate(0, κ_RR)`.
   - Theorem 1 gives `ψ <= K_RR γ_0^2 <= K_RR γ^2`, which is membership in
     `Rate(K_RR, 0)`.
   - The remaining statements are items 3 and 4 of
     `expansion-certified-repetition-caps-deficit-ratio`, applied verbatim. ∎

**Remark (the statement-level reading).** Theorem 2 as stated only says
`(1 − ε)^(poly(λ) n)`, with the polynomial left implicit. The alternative
argument posted live by `swarm-0917-w17-w17-ugc-last1` forces
`poly(0) = 0` through the odd cycle `C_m`, whose gap is
`λ_RR = sin^2(π/m)`.

That argument needs Raz--Rosen's hypothesis, "uniform over the edges of a
(biregular) bipartite" graph, to cover `C_m`. `C_m` puts weight `1/2` on
`y = x`, so it is uniform only over the edges of a multigraph. The obvious
simple-graph splitting gives Bob the vertices `(y, j)`, with Alice's `x`
joined to `(x,0)`, `(x,1)`, `(x+1,2)` and `(x−1,3)`. Bob then learns `x` on
the `j = 2, 3` edges, so that splitting has value 1.

The proof-level reading above needs no such step. It gives the explicit
polynomial, and nothing is left to a reading of `poly`.

**Invariant and death step.** This is the same as in the kill. The invariant
is the normalized certified rate `ψ/η`. Raz--Rosen buy linearity in `ε` by
first amplifying to a deficit of order `λ`, which costs `m = Θ(log(2/λ)/(ελ^2))`
rounds, and then running Rao. The resulting rate is at most `λ^3` times the
AKKSTV-type shape `λγ`. It dies at soundness certification, where hard
λ-gapped sources force `λγ <= 1592 η`.
