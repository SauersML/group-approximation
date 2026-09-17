---
rg: 2
id: thompson-f-cnd-certificates-need-near-exponential-ball-growth
kind: claim
title: Every conditionally negative definite function on Thompson's group F has balls of almost exponential size
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that is Moore's lower bound on Følner sets, used here as input; this transfers it to return probabilities and to the ball growth of every cnd function.
  thompson-f-moment-data-cannot-certify-nonamenability: that shows finite cogrowth data cannot prove non-amenability; this bounds return probabilities of F from above and kills a class of amenability certificates.
  cnd-ball-growth-bounds-return-probability-for-every-group: that is the group-independent inequality; this is its combination with Moore's theorem for F.
  thompson-f-is-amenable: that is the open question; this is unconditional and decides nothing about it.
---

**ESTABLISHED (unrefereed).**

**Setting.**
- `Γ ⊆ F` is a finite symmetric generating set, and `C > 1` is Moore's constant for `Γ`.
- `mu = 1/2 delta_e + (1/(2|Γ|)) sum_{γ in Γ} delta_γ` is the lazy walk, and `p_k = mu^{*k}(e)`.
- `exp_0(0) = 0`, `exp_{j+1}(0) = 2^{exp_j(0)}`, and `l(x) = min{ j : exp_j(0) > x }`.
- `L = log_2(|Γ| + 1)`.

**Theorem A (return probability).** For every `N >= 1`,
`p_{2N} <= exp( - N C^{-2(1 + l(N L))} / (16 |Γ|^2) )`.

**Theorem B (cnd ball growth).** Let `psi` be conditionally negative definite on `F` with `psi(e) = 0`,
and put `c = E_mu psi`. Then either `psi ≡ 0`, or `c > 0` and for every `N >= 1`,
`|{g : psi(g) <= 2cN}| >= (1/4) exp( N C^{-2(1 + l(N L))} / (16 |Γ|^2) )`.

**Corollary (the class kill).** Let `g`, positive for large `R`, satisfy `log g(R) / log* R -> inf`.
For example, `g` can be any fixed iterate `log^{(k)}`, any power `R^a` with `a > 0`, or `log R`.
Then no cnd `psi` on `F` with finite balls satisfies
`log |{psi <= R}| <= R / g(R)` for all large `R`.

In words: an amenability certificate for `F` of Gaussian type is ruled out whenever its growth
profile is sub-exponential by more than a factor `C^{O(log* R)}`. Such a certificate is either
- `e^{-t psi} in l^2(F)` for all `t > 0`, or
- a cnd `psi` with `log|B_R| = o(R)`

(see `cnd-ball-growth-bounds-return-probability-for-every-group`).

**What the kill covers.** The invariant is the ψ-ball growth profile. Every member dies at one step:
- the Markov-type-2 second moment bound turns small balls into large return probabilities;
- Følner extraction from the walk, plus Moore's theorem, forbids large return probabilities at
  computable scales.

This excludes every elementary sub-exponential profile, including:
- polynomial growth;
- `exp(R/log R)`;
- `exp(R / log^{(k)} R)`.

It also excludes proper cnd functions coming from explicit geometric actions with such profiles. The
exponential-growth ones, such as Farley's CAT(0) cube complex, already fail trivially.

**What survives.** Profiles `log |B_R| = R / g(R)` with `g(R) <= C^{O(log* R)}`. This is the same survivor
band as for Følner sets in `thompson-f-folner-function-exceeds-every-tower`. A Gaussian proof of
amenability would have to produce a cocycle whose balls are exponential up to a factor `C^{O(log* R)}`
in the exponent, and would have to control that factor exactly.

**Remark (numerics).**
- *Height of `l`.* `l(N L) <= 5` whenever `N L < 65536`.
- *Scale of the rate.* At every length that can be computed, Theorem A only gives decay at rate at least
  `C^{-12} / (16|Γ|^2)`, with `C` unknown. So measured cogrowth decay at such lengths is consistent with
  Theorem A whatever the truth is.
- *Why this matters.* Theorem A also shows that, if `F` is amenable, `-log p_{2N}` is at least
  `N C^{-2(1+l(NL))}/16|Γ|^2`. That is linear in `N` up to a factor which is constant over every
  computable range. Numerical near-exponential decay of cogrowth is therefore not evidence against
  amenability.
- *Not a claim.* This remark is recorded as an interpretation, not as a claim.

**Scope.** It depends on Moore's theorem as cited in `thompson-f-folner-function-exceeds-every-tower`
(proof not re-read there). Deriving return-probability bounds from Følner/isoperimetric profiles is
classical (Coulhon–Saloff-Coste style); novelty of technique is not claimed.

Proof route: `thompson-f-cnd-ball-growth-from-folner-tower`.
