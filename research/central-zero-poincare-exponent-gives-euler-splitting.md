---
rg: 2
id: central-zero-poincare-exponent-gives-euler-splitting
kind: claim
title: "If some cnd function on G has zero Poincare exponent along the central cyclic subgroup <z>, then G/<z> has a nonsingular space with almost invariant Koopman vectors over which the extension splits measurably with an integer cocycle"
distinct_from:
  central-extension-haagerup-from-measurable-euler-splitting: that goes from a measurable splitting over an almost invariant space to the Haagerup property of G; this goes the other way, from a cnd function that grows fast on the centre to such a splitting, by a nonsingular Gaussian action
  thompson-t-euler-class-splits-over-almost-invariant-space: that is the specific open statement (MT) for Thompson's T; this is a general theorem that produces (MT)-type witnesses from central growth of one cnd function
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that is the discrete (countable coset space) case of (MT); the witness here is a fundamental domain of a dissipative Gaussian action, which has no atoms
  cantor-integer-maps-central-growth-criterion: that characterizes unboundedness of a cnd function on a central direction spectrally; this needs a quantitative (superlogarithmic) growth and outputs a measurable splitting
artifacts: []
---

**ESTABLISHED** by `central-zero-poincare-exponent-gives-euler-splitting-proof`.

**Setting.** `G` is a countable group, `z ∈ G` is central of infinite order, `Q = G/⟨z⟩`.
For a cnd function `ψ` on `G` (with `ψ(e) = 0`) define the *central Poincaré exponent*

    δ_z(ψ) = inf { s > 0 : Σ_{m ∈ Z} exp(−s ψ(z^m)) < ∞ }  ∈ [0, ∞].

**Condition (SL).** Some cnd function `ψ` on `G` has `δ_z(ψ) = 0`, that is
`Σ_m exp(−s ψ(z^m)) < ∞` for every `s > 0`. This holds when `ψ(z^m)/log|m| → ∞`. Conversely, if
`ψ(z^m) ≤ C log|m|` for all large `|m|`, then the sum diverges at `s = 1/C`, so `δ_z(ψ) ≥ 1/C`.
So (SL) sits between `limsup ψ(z^m)/log|m| = ∞` and `lim ψ(z^m)/log|m| = ∞`. It is
"superlogarithmic growth on the centre".

**Theorem.** Assume (SL). Then there are
- a standard σ-finite measure space `(W, μ)` with a nonsingular action of `Q` whose Koopman
  representation `(κ(q)F)(w) = RN_q(w)^{1/2} F(q^{-1}w)` has almost invariant unit vectors;
- a measurable `β : G × W → Z`, with `G` acting through `Q`, such that
  `β(gh, w) = β(g, h·w) + β(h, w)` for all `g, h` and all `w`, and `β(z, w) = 1` for all `w`.

So (SL) produces exactly the hypotheses 2 and 3 of
`central-extension-haagerup-from-measurable-euler-splitting`, with an integer-valued `β`.

**Equivalent forms of (SL).**
- (SL) is equivalent to (SL*): for every finite `F ⊂ G` and `ε > 0` there is a cnd `ψ` with
  `ψ ≤ ε` on `F` and `δ_z(ψ) < 1/8`. For the converse direction, take `ψ_j` for `(F_j, 2^{-j}/j)`,
  with `F_j` exhausting `G`. Then `ψ = Σ_j j ψ_j` converges pointwise and is cnd, and
  `δ_z(ψ) ≤ δ_z(j ψ_j) = δ_z(ψ_j)/j < 1/(8j)` for every `j`.
- `δ_z(cψ) = δ_z(ψ)/c` and `δ_z` is monotone decreasing in `ψ`.

## Consequences

- **General criterion.** If `Q` has the Haagerup property and (SL) holds, then `G` has the Haagerup
  property. This follows from the Theorem and `central-extension-haagerup-from-measurable-euler-splitting`.
- **Thompson's T-bar.** Let `G = T̄` and `Q = T`, which is Haagerup by `thompson-v-has-haagerup-property`.
  Then (SL) for `T̄` implies (MT) (`thompson-t-euler-class-splits-over-almost-invariant-space`),
  hence `lifted-thompson-t-is-a-t-menable`. The Haagerup property of `T̄` implies a cnd function
  that is proper on `⟨z⟩`. So the Haagerup property of `T̄` lies between two growth conditions on
  one cnd function along the centre:

      (SL)  ⇒  (MT)  ⇒  T̄ Haagerup  ⇒  some ψ with ψ(z^m) → ∞.

  The only gap between the ends is the rate: superlogarithmic against merely unbounded. The open
  node for the left end is `lifted-thompson-t-has-cnd-with-zero-central-poincare-exponent`.
- **Forced shape, consistent.** For `G = T̄`, (F1) of the (MT) node forces `β(g, ·)` to fail
  uniform integrability along the almost invariant densities. Here `β(g, w)` is the number of
  fundamental-domain translates that `g` jumps over at `w`, and the construction puts no bound on it.

## Attempts

- 2026-09-18 (swarm-0917-w13-w13-nv-last1): proved as stated; see the proof route. The dissipativity
  step is Theorem B of Arano–Isono–Marrakchi, quoted verbatim in the proof.
