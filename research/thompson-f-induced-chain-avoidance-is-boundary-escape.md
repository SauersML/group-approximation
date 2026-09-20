---
rg: 2
id: thompson-f-induced-chain-avoidance-is-boundary-escape
kind: claim
title: For a step distribution on Thompson's group F with generating semigroup, the induced chain avoids some interval with positive probability exactly when it escapes to the endpoints with positive probability, so interval avoidance fails for every symmetric finitely supported walk
distinct_from:
  thompson-f-interval-avoiding-walks-have-positive-entropy: that proves positive entropy assuming the avoidance probability theta is positive; this shows theta > 0 is equivalent to escape of the induced chain to the endpoints, and that theta = 0 for every interval for all symmetric finitely supported walks, so the hypothesis of that theorem is never met there.
  thompson-f-dyadic-orbit-walks-are-transient: that is transience on points of the dyadic orbit; this is about the real topology, where the same chain is recurrent to compact sets and enters every open interval infinitely often, and it uses transience only to turn escape back into avoidance.
  thompson-f-finite-entropy-walks-are-not-liouville: that is the open finite-entropy rung; this refutes prerequisite (B) of its recorded decomposition and does not decide the rung.
  f-dyadic-action-is-not-recurrent: that is linear growth of inverted orbits on dyadic points; this is recurrence of the same chain to compact subintervals, which holds at the same time.
---

**ESTABLISHED.** Notation.

- `D` is the set of dyadic rationals in `(0,1)`.
- `d(t) = min(t, 1−t)`.
- For a probability measure `µ` on `F`, the *induced chain* from `t ∈ (0,1)` is `Z_0 = t`, `Z_k = h_k(Z_{k−1})`, with
  `h_k` i.i.d. of law `µ`. This is the chain of `thompson-f-interval-avoiding-walks-have-positive-entropy`.
- For dyadic `x < y` put `θ_{[x,y]} = P_x(Z_k ∉ [x,y] for all k ≥ 1)`.
- `Esc = {d(Z_k) → 0}` is the event that the chain escapes to the endpoints.

**Theorem 1 (avoidance is boundary escape).** Let `µ` be any probability measure on `F` with `sgr supp µ = F`. No
moment, entropy, support or symmetry condition is imposed.

1. (Alternative.) For every `t ∈ (0,1)` and every nonempty open interval `J ⊂ (0,1)`, `P_t`-almost surely either
   `d(Z_k) → 0` or `Z_k ∈ J` for infinitely many `k`.
2. (Upper bound.) `θ_{[x,y]} ≤ P_x(Esc)` for all dyadic `x < y`.
3. (Lower bound.) `lim_{y↓x} θ_{[x,y]} = (1 − r_x) P_x(Esc)`, where `r_x = P_x(Z_k = x for some k ≥ 1) < 1`.
4. (Equivalence.) The following are equivalent:
   - `θ_{[x,y]} > 0` for some dyadic `x < y`, which is prerequisite (B) for `µ`;
   - `P_z(Esc) > 0` for some `z ∈ D`;
   - `P_z(Esc) > 0` for every `z ∈ D`.

**Theorem 2 (germ-recurrent walks never avoid).** Let `µ` satisfy `sgr supp µ = F`. Assume there are `r > 0` and
`A < ∞` such that every `h ∈ supp µ`

- is linear on `[0,r]` and on `[1−r,1]`, and
- has `|log2 h'(0)| ≤ A` and `|log2 h'(1)| ≤ A`.

Assume also that the germ drifts satisfy `χ_0 = E_µ log2 h'(0) ≥ 0` and `χ_1 = E_µ log2 h'(1) ≥ 0`. Then
`P_t(Esc) = 0` for every `t ∈ (0,1)`. So for every `t` and every nonempty open `J`, the chain from `t` enters `J`
infinitely often almost surely, and `θ_{[x,y]} = 0` for all `x < y`.

The hypotheses hold for every finitely supported `µ` with `χ_0, χ_1 ≥ 0`. In particular they hold for every
**symmetric finitely supported** `µ` with `sgr supp µ = F`, where `χ_0 = χ_1 = 0`. An example is the uniform measure
on `{x0^{±1}, x1^{±1}}`.

**Corollary 3 (prerequisite (B) is false).** Prerequisite (B) of the recorded decomposition of
`thompson-f-finite-entropy-walks-are-not-liouville` reads: "for every finite-entropy generating `µ`, some
`θ_{[x,y]} > 0`". It fails for the simple random walk on `{x0^{±1}, x1^{±1}}`, which has finite entropy and
generating support.

It also fails on infinitely supported measures outside the killed finite-moment rung. Here is an example.

- Let `k_N ∈ F` be supported in `[1/4, 3/4]`, with `|Br(k_N)| ≥ 4^N`. Such elements exist: take products of
  bumps with pairwise disjoint supports, taking `4^N` of them. Each bump has at least 2 breakpoints.
- Let `µ` be half the uniform measure on `{x0^{±1}, x1^{±1}}` plus half of `Σ_N w_N (δ_{k_N} + δ_{k_N^{-1}})/2`, with
  `w_N ∝ 2^{-N}/N²`.

This `µ` has the following properties.

- It is symmetric and generating, with `H(µ) < ∞`.
- `E_µ|Br(h)| ≥ Σ w_N 4^N = ∞`, so condition 2 of `thompson-f-finite-breakpoint-moment-walks-are-not-liouville`
  fails.
- It satisfies Theorem 2 with `r = 1/8` and `A = 1`, so `θ_{[x,y]} = 0` for every interval.

Neither recorded non-Liouville mechanism, as stated, applies to this `µ`. The Green-weighted "sharper form" of the
breakpoint rung is unchecked for it.

**What dies.** The class that dies consists of the positive-entropy detectors whose readable event requires the
induced chain to stay out of a fixed nonempty open interval forever, or from some time on. On every `µ` with
`P(Esc) = 0` that event has probability `0`, by Theorem 1.1. This covers:

- the uncovered-endpoint detector of `thompson-f-interval-avoiding-walks-have-positive-entropy`;
- its variants for the lazy measure `(µ+δ_e)/2`, since the lazy chain visits the same points.

The invariant is `limsup d(Z_k) > 0` (compact recurrence) together with the minimality of `F ↷ (0,1)`. The dying
step is `θ > 0`.

The corollary of `thompson-f-interval-avoiding-walks-have-positive-entropy` (a finite-entropy Liouville witness
approaches every dyadic from the right) is by Theorem 1 the statement `P(Esc) = 0`. That is shared by every
symmetric finitely supported walk, all of which are non-Liouville. So it constrains nothing.

**What survives.** Detectors that read something other than forever-avoidance of a fixed interval survive. Examples:

- multi-scale detectors `Δ = {e, b_L}`, where the summability of first-entry times into `[x, x+2^{-L}]` replaces
  avoidance;
- breakpoint-content detectors;
- the Green-weighted breakpoint bound.

Any proof of the finite-entropy rung must work on compact-recurrent chains, and in particular on the symmetric
infinite-breakpoint family of Corollary 3.

Proof: `thompson-f-induced-chain-avoidance-is-boundary-escape-proof`.
