---
rg: 2
id: fpbs-relative-dt-green-threshold-splits-identity-e
kind: claim
title: The Green function of the pushed-forward DT boundary measure defines a threshold between the quotient l2 threshold and the relative threshold, which splits Claim E into relative DT sharpness and finite-volume no-drift, and on nonunimodular horocycles it sees the whole window up to p_t
distinct_from:
  fpbs-quotient-dt-threshold-is-quotient-l2-threshold: that certifies with the l2(Q) spectral radius of the pushed DT measure and proves its threshold is p^Q; this certifies with the Green function (return rate) of the same measure, a weaker non-l2 condition whose threshold p^G can exceed p^Q, and proves p^Q <= p^G <= p_c(N;G).
  fpbs-quotient-spectral-dt-certificates-are-subgroup-blind: that kills Schreier spectral certificates because their relative version implies the absolute one; the Green certificate escapes this, since a return rate is not a spectral radius and the absolute (N = 1) Green certificate carries no information.
  fpbs-relative-threshold-is-quotient-l2-threshold: that is the open Claim E; this proves E is the conjunction of two statements that can fail independently, and shows the known off-Cayley failure of E is a failure of the second one only.
  fpbs-nonunimodular-level-sets-break-identity-e: that computes p^(l2), p^(diag) and p_c(L;G) on nonunimodular level sets; this adds the finite-volume Green threshold p^G(L) >= p_t, with an explicit ball certificate on T_k, so the calibration no longer needs full multi-chain susceptibilities.
  fpbs-transitive-sharpness-linear-lower-bound: that is DT's sharpness for the whole graph (imported through the route fpbs-duminil-copin-tassion-sharpness-input); the case Q trivial of relative DT sharpness (E-a) below is exactly DT's identity p~_c = p_c.
artifacts:
  - experiments/fpbs-green-dt-2026-09-17/horocycle_green_dt.py
  - experiments/fpbs-green-dt-2026-09-17/horocycle_threshold_scan.py
---

**ESTABLISHED** (proof: `fpbs-relative-dt-green-threshold-splits-identity-e-proof`).

**Setting.** As in `fpbs-quotient-dt-threshold-is-quotient-l2-threshold`:
`G = Cay(Gamma, D)`, `N` an infinite normal subgroup, `Q = Gamma/N`,
`pi : Gamma -> Q`, and for finite `S` containing `o`

```text
nu_{S,p}(g) = p * sum_{ {u,v} in Delta S, v = g } P_p(o <->_S u),
mu_{S,p} = pi_* nu_{S,p},     a_S = pi_* 1_S          (finitely supported on Q),
D_p(S) = sum_{k>=0} (mu_{S,p}^{*k} * a_S)(e_Q)        in [0, infinity],
r_p(S) = limsup_k ((mu_{S,p}^{*k} * a_S)(e_Q))^(1/k),
p^G(N;G) = sup{p : some finite S containing o has D_p(S) < infinity}.
```

`D_p(S)` is the Duminil-Copin--Tassion majorant of the relative
susceptibility `chi^N_p = E_p|K_o ∩ N|`. It involves only returns of the
`mu`-chain to `e_Q`, never an operator norm on `l2(Q)`.

**Theorem.**

1. **The Green certificate bounds the relative susceptibility.**
   `chi^N_p <= D_p(S)` for every `p` and every finite `S` containing `o`.
2. **Strict monotonicity and openness.** Let `m(S)` be the number of edges
   with both endpoints in `S`. For `0 < p < p' < 1`, entrywise,
   `mu_{S,p} <= (p/p') mu_{S,p'}` and
   `mu_{S,p'} <= (p'/p)^(m(S)+1) mu_{S,p}`. Hence
   `r_p(S) <= (p/p') r_{p'}(S)` and `r_{p'}(S) <= (p'/p)^(m(S)+1) r_p(S)`, and
   `{p : some S has r_p(S) < 1} = [0, p^G(N;G))`, an open interval with the
   same supremum as `{p : some S has D_p(S) < infinity}`.
3. **The chain.**

   ```text
   p_c(G) <= p^Q_(2->2)(N;G) <= p^G(N;G) <= p_c(N;G).
   ```

4. **The split of Claim E.** `E(G,N)` holds if and only if both
   * **(E-a) relative DT sharpness:** `p^G(N;G) = p_c(N;G)`, and
   * **(E-b) finite-volume no-drift:** `p^G(N;G) = p^Q_(2->2)(N;G)`.

   Both hold when `Q` is amenable, where all four thresholds equal `p_c`. When
   `Q` is trivial (`N = Gamma`), `mu_{S,p} = phi_p(S) delta_e` with `phi_p(S)`
   DT's boundary sum, `D_p(S) = |S| / (1 - phi_p(S))` when `phi_p(S) < 1`, and
   `p^G` is DT's `p~_c`. So (E-a) is literally the relative form of the
   Duminil-Copin--Tassion theorem `p~_c = p_c`.
5. **A critical Green certificate is a Kesten gap.** Some finite `S` has
   `r_{p_c}(S) < 1` if and only if `p_c < p^G(N;G)`. Either one implies
   `p_c < p_c(N;G)` and hence `p_c(G) < p_u(G)`
   (`fpbs-relative-gap-along-any-subgroup-separates`). Under (E-a) the Kesten
   gap along `N` is equivalent to such an `S`.
6. **Type (ii) is a drift gap.** Under (E-a), `E(G,N)` fails if and only if
   `p^Q < p^G`, and `(G,N)` is of type (ii) in C1 of
   `fpbs-relative-threshold-is-quotient-l2-threshold`
   (`p_c = p^Q < p_c(N;G)`) if and only if `p_c = p^Q < p^G`. Such a pair has
   some `S` with `r_{p_c}(S) < 1`, while every `S` has
   `sp_Q(mu_{S,p_c}) >= 1`. The pushed critical measure then returns to
   `e_Q` at exponential rate below one although its `l2(Q)` spectral radius
   is at least one, which is a genuine drift.
7. **The epsilon-diagonal form of p^Q.** If `S` and `eps > 0` satisfy
   `G_eps := sum_n (mu_{S,p} + eps a_S)^{*n}(e_Q) < infinity`, then
   `||sigma^N_p||_Q <= 1/eps` and `D_p(S) <= G_eps / eps`. Conversely every
   `p < p^Q` has such `S` and `eps`. So

   ```text
   p^Q_(2->2)(N;G) = sup{p : some S and some eps > 0 have G_eps < infinity},
   p^G(N;G)        = sup{p : some S has D_p(S) < infinity},
   ```

   and (E-b) says exactly that a finite return certificate survives, after an
   arbitrarily small decrease of `p`, the addition of a small multiple
   `eps a_S` of the `S`-mass to the step measure. Both certificates are
   statements about returns to `e_Q` alone. The only difference is where the
   `S`-mass may appear in the chain: at the end only, or between any two
   steps.
8. **Nonunimodular calibration.** Let `Gamma ⊆ Aut(G)` be transitive and
   nonunimodular on a connected locally finite `G`, with `Delta`, `delta`,
   `N_Delta` and the level set `L = N_Delta o` as in
   `fpbs-nonunimodular-level-sets-break-identity-e`, and let
   `Lambda = delta(Gamma) ⊆ (0, infinity)`. Push `nu_{S,p}` and `1_S` to
   `Lambda` by `h(y) = Delta(o,y)`, and define `D_p(S)` and `p^G(L)` as above.
   Then `sum_(x in L) tau_p(o,x) <= D_p(S)`, and

   ```text
   p^(l2)(L) = p_T <= p_c(G) < p_t <= p^G(L) <= p_c(L;G).
   ```

   On `T_k` (`k >= 3`) with the horocycle of an end, the ball `B_R` has
   pushed measure of total mass `p^(R+1) k (k-1)^R` (above one for every
   `p > 1/(k-1)` and large `R`), and at `lambda = (1/2) log(k-1)` the Laplace value

   ```text
   Phi_R(p) = (p sqrt(k-1))^(R+1) * (2 + R (k-2)/(k-1)),
   ```

   which tends to `0` for every `p < 1/sqrt(k-1)`. So
   `p^G(L) = p_t = p_c(L;T_k) = 1/sqrt(k-1)`, while
   `p^(l2)(L) = p_c(T_k) = 1/(k-1)`. The analogue of (E-a) holds there, and
   the analogue of (E-b) fails on the whole window `(p_c, p_t)`.

## What this changes

- **A finite-volume Kesten certificate that is not an l2 condition.** C1 of
  `fpbs-relative-threshold-is-quotient-l2-threshold` says any proof of the
  Kesten premise on a type (ii) pair must see "a relative gap that is not an
  l2 gap". Item 5 supplies such an object. It is one finitely supported
  measure on `Q` with polynomial coefficients at `p_c`, and it certifies the
  gap by its return rate alone. Item 8 shows that such certificates exist
  strictly beyond every l2 certificate in the transitive world: on `T_k`
  horocycles they reach `p_t`, although the l2 threshold is `p_c`.
- **The split is proper.** (E-a) and (E-b) are separate statements, and item
  8 shows that (E-b) can fail while (E-a) holds (on a transitive pair). On
  `T_k` horocycles, the failure of E found in
  `fpbs-nonunimodular-level-sets-break-identity-e` is entirely a failure of
  (E-b). On other nonunimodular pairs, item 8 still puts at least the window
  `(p_c, p_t)` into the failure of (E-b). The Cayley-only input that
  separates the cases is `tau(x^(-1)) = tau(x)` (item (0d) of the sandwich
  proof). The pushed DT measure `mu_{S,p}` does
  not inherit that symmetry, which is why (E-b) is not automatic.
- **(E-a) is DT's theorem with a quotient.** For `Q` trivial it is
  `p~_c = p_c`. For amenable `Q` it holds by
  `fpbs-amenable-quotient-normal-relative-threshold-is-pc`. On `T_k`
  horocycles its transitive analogue holds. Nothing seen so far contradicts
  it on any transitive pair. Claim E is then equivalent to (E-b) on every
  graph where (E-a) is proved.

## Where each half can fail (invariants)

- **(E-a)** fails at `(G,N,p)` if `chi^N_p < infinity` (so
  `p < p_c(N;G)`), yet for every finite `S` the chain of `mu_{S,p}`
  returns to `e_Q` at rate at least one. The invariant is the return rate
  `inf_S r_p(S)`. A DT-type proof has to make `inf_S r_p(S) >= 1`
  propagate to `chi^N = infinity` slightly above `p`. DT's one-step
  differential inequality handles the case `Q` trivial, where the rate is the
  total mass `phi_p(S)`. For nontrivial `Q` the rate is the return rate of a
  non-symmetric chain on `Q`, not a single mass, and the one-step inequality
  does not see it. That step is the open core, recorded as
  `fpbs-relative-dt-sharpness`.
- **(E-b)** fails at `(G,N)` if some `S` has `r_p(S) < 1` at a `p` with
  `||sigma^N_p||_Q = infinity`. The invariant is the gap between the return
  rate and the l2 spectral radius of `mu_{S,p}`. On `T_k` horocycles at
  `p in (1/(k-1), 1/sqrt(k-1))`, the spectral radius of `mu_{B_R,p}` (its
  total mass, since `Z` is amenable) tends to infinity with `R`, while the
  Chernoff bound on its return rate tends to `0`. Recorded as
  `fpbs-finite-volume-no-drift`.
