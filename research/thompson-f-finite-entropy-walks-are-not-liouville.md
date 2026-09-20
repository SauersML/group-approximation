---
rg: 2
id: thompson-f-finite-entropy-walks-are-not-liouville
kind: claim
title: Every finite-entropy step distribution on Thompson's group F whose support generates F as a semigroup is non-Liouville
distinct_from:
  thompson-f-finite-breakpoint-moment-walks-are-not-liouville: that covers measures with finite expected breakpoint count; this asks for all measures of finite Shannon entropy, which allows infinite breakpoint moments at every dyadic point.
  thompson-f-interval-avoiding-walks-have-positive-entropy: that proves the conclusion under an extra avoidance hypothesis on the induced chain; this is the unconditional statement.
  thompson-f-is-not-amenable: that is non-amenability, which forbids Liouville measures of every kind; this only forbids finite-entropy ones, and it would not decide amenability, since some amenable groups admit no finite-entropy Liouville measure (Erschler 2004).
---

**OPEN.** Let `µ` be a probability measure on `F` with `H(µ) < ∞` and `sgr supp µ = F`. Then `(F, µ)` has a
nonconstant bounded harmonic function.

Kaimanovich (arXiv:1602.02971v2, §7.A) asks for the analogous statement on lamplighters, verbatim: "Apparently, it
is not known whether the Poisson boundary on lamplighter groups is non-trivial for all step distributions with
finite entropy provided the quotient random walk is transient."

This is the next rung after `thompson-f-finite-breakpoint-moment-walks-are-not-liouville`. Any symmetric Liouville
measure witnessing amenability must lie outside every rung that has been killed.

## Attempts

- **2026-09-17, conjugated bump insertions (swarm-0917-w5-f-l2-proper).** The claim splits into two prerequisites,
  and each can fail on its own.
  - **(A) Avoidance gives entropy.** Suppose the induced chain `z ↦ h(z)` from some dyadic `x` avoids some `[x,y]`
    with positive probability. Then `h((µ+δ_e)/2) > 0`, so `µ` is non-Liouville. This is ESTABLISHED as
    `thompson-f-interval-avoiding-walks-have-positive-entropy`.
    - Method: insert a copy `b` of `x_0` on `[x,y]` as a `Δ`-letter. Conditioned on the other letters, `X_n` is a
      product of conjugates `b_i^{S_i}` times known words.
    - The exponent `S_i` can be read from the breakpoint jump at the left endpoint `x_i` of `supp b_i`, provided `x_i`
      is not covered by an earlier support.
    - A run is uncovered with probability at least `θ/2`, which gives linear conditional entropy. No breakpoint
      moment is used.
  - **(B) Avoidance holds.** For every finite-entropy generating `µ`, some `θ_{[x,y]} > 0`. This is open.
    - Its negation is forced on a counterexample by the corollary of (A): if `µ` is Liouville, then from every start
      the chain's path a.s. approaches every dyadic from the right, while staying transient on points.
    - Invariant: the uncovered left endpoint of the conjugated support.
    - Dies at: real-topology accumulation of the induced chain. Transience
      (`thompson-f-dyadic-orbit-walks-are-transient`) controls visits to points, not to intervals. Kaimanovich's
      convergence to ends (Theorem 38) needs finite support and says nothing about the real topology.
    - This parallels Erschler–Frisch (arXiv:2206.11111v3, Remark 9.9): transience alone is not enough for linear
      `Δ`-entropy.
  - Not covered here, and still possible (unchecked):
    - detectors that do not use endpoints, for example the breakpoint content of the whole support;
    - several scales `Δ = {e, b_L : L ≥ 1}`, whose covering probabilities could replace forever-avoidance by a
      summability condition. Such a detector must still beat dense accumulation, and it depends on how much mass
      `µ^{*k}` puts on small bumps at `x`.
- **2026-09-17, (B) refuted: avoidance is boundary escape (swarm-0917-w20-w20-f-pull, probability-random).**
  Prerequisite (B) of the w5 decomposition is false, so the (A)+(B) route is dead. This is ESTABLISHED as
  `thompson-f-induced-chain-avoidance-is-boundary-escape`.
  - For every generating `µ`, `F ↷ (0,1)` is minimal and every element is a positive word. So from each compact
    `K ⊂ (0,1)` the chain hits any open `J` within `N` steps with probability at least `c > 0`.
  - Hence, almost surely, either `d(Z_k) → 0` or the chain enters `J` infinitely often.
  - Combined with transience and a last-exit count at `x`, this gives
    `lim_{y↓x} θ_{[x,y]} = (1 − r_x) P_x(d(Z_k) → 0)`.
  - So (B) holds for `µ` if and only if the induced chain escapes to `{0,1}` with positive probability.
  - For a walk whose support elements are linear on a uniform `[0,r] ∪ [1−r,1]`, with bounded germ exponents and germ
    drifts `≥ 0`, the endpoint germ walk cannot drift to `−∞` (weak law or CLT, then Hewitt–Savage). So escape has
    probability `0`, and `θ_{[x,y]} = 0` for every interval.
  - This covers every symmetric finitely supported walk, and in particular the simple random walk on
    `{x0^{±1}, x1^{±1}}`, which has finite entropy and is generating. It also covers the auxiliary `ν`-chain of the
    (A) proof.
  - It also covers a symmetric finite-entropy measure with `E|Br| = ∞`: the simple random walk mixed with bumps
    `k_N` in `[1/4,3/4]`, where `|Br(k_N)| ≥ 4^N` and the weights are `∝ 2^{-N}/N²`. On this measure neither
    recorded mechanism applies as stated, which makes it a calibration target for this rung.
  - Invariant: compact recurrence `limsup d(Z_k) > 0`, plus minimality.
  - Dies at: `θ > 0`. The same happens for every detector that reads forever-avoidance, or eventual avoidance, of a
    fixed open interval.
  - The corollary of (A), that a Liouville witness approaches every dyadic from the right, is equivalent to
    `P(Esc) = 0`. That holds for all symmetric finitely supported walks, so it constrains nothing.
  - Survivors:
    - multi-scale first-entry summability for `Δ = {e, b_L}`;
    - breakpoint-content detectors;
    - the Green-weighted breakpoint bound, whose value on the calibration family is unchecked.
