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
