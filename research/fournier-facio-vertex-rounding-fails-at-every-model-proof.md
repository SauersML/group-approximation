---
rg: 2
id: fournier-facio-vertex-rounding-fails-at-every-model-proof
kind: route
title: Genuine finite-dimensional representations kill the simple factor, and rounding transports that to the model
target: fournier-facio-vertex-rounding-fails-at-every-model
requires: [fg-infinite-simple-groups-are-minimally-almost-periodic, fournier-facio-torsion-free-skeleton]
---

**Step 1 (inputs).** By `fournier-facio-torsion-free-skeleton`, `Gamma = pi(P)` has property (T),
so it is finitely generated, say by `F_Gamma`. It contains `pi(S)`, an injective image of a finitely
presented, hence finitely generated, infinite simple group `S`.

**Step 2 (genuine representations kill `pi(S)`).** Let `pi_n : Gamma -> U(n')` be a genuine
representation. Its restriction to `pi(S)` is a homomorphism of a finitely generated infinite simple
group into the compact group `U(n')`. By `fg-infinite-simple-groups-are-minimally-almost-periodic`
it is trivial, so `pi_n(s) = 1` for every `s in pi(S)`.

**Step 3 (rounding transports the triviality).** Assume (H1) at `sigma`, and write
`sigma'_n = sigma_n (+) 1_(n' - n)`, so `||sigma'_n(f) - pi_n(f)||_2 -> 0` for `f in F_Gamma`, and hence for
`f^-1` by unitarity. Fix `s in pi(S)` and a word `s = f_1 ... f_k` with each `f_j` in
`F_Gamma union F_Gamma^-1`. Since the normalized 2-norm is unitarily invariant,

```text
||sigma'_n(f_1) ... sigma'_n(f_k) - pi_n(f_1) ... pi_n(f_k)||_2
   <=  sum_j ||sigma'_n(f_j) - pi_n(f_j)||_2  ->  0 .
```

The right-hand product is `pi_n(s) = 1`. On the first `n` coordinates the left-hand product
represents `sigma(s)` along `U`, and the padding carries normalized weight `(n' - n)/n' -> 0`. Hence
`sigma(s) = 1` in `prod_U M_n`.

**Step 4 (faithful models).** If `sigma` is the restriction of a trace-preserving homomorphism of
`G`, then `tau(sigma(s)) = 0` for `s != 1`, so `sigma(s) != 1`, and (H1) fails at `sigma`.
