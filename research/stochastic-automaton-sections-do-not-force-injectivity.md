---
rg: 2
id: stochastic-automaton-sections-do-not-force-injectivity
kind: claim
title: On every group with an element of infinite order, a surjective non-injective automaton has a faithful Bernoulli-preserving equivariant Markov section, so the Markov hull of the automaton monoid is not directly finite, while the decoder-side Markov relaxation is equivalent to surjunctivity
distinct_from:
  directly-finite-ring-images-of-ca-monoids-kill-retracts: that node notes that the pullback representation lands in End of an infinite-dimensional space; this one shows direct finiteness already fails inside the positive, unital, equivariant, local, Bernoulli-preserving hull of the Koopman image on Z, and says which side of the pair may be relaxed.
  surjunctivity-iff-automaton-monoid-directly-finite: that node is the deterministic equivalence; this one relaxes one factor to Markov operators and finds a split, since the encoder relaxation is false and the decoder relaxation is equivalent.
artifacts:
  - research/artifacts/stochastic-sections-of-automata-2026-09-20.md
  - experiments/markov-section-2026-09-17/check_markov_section.py
---

Let `Mark(G, A)` be the monoid of shift-equivariant Markov operators on
`C(A^G)`, that is, positive unital linear maps, or equivalently Feller
kernels. Koopman operators `f -> f o phi` of cellular automata are exactly
the multiplicative elements of `Mark(G, A)`.

**Encoder relaxation is false.** Let `s` in `G` have infinite order, let
`n >= 2`, and let `sigma(x)_g = x_g - x_{gs}` on `(Z/n)^G`. Then `sigma` is
onto, and its kernel `K` (the configurations constant on the cosets `g<s>`)
is nontrivial. Averaging over the fibre `sigma^{-1}(y) = x_y + K` with Haar
measure gives `T` in `Mark(G, Z/n)` with the following properties:

- `T sigma^* = 1`, while `sigma^* T` is the Haar conditional expectation
  onto the `K`-invariant functions, so `sigma^* T != 1`;
- `T` is faithful and preserves the uniform Bernoulli measure;
- `T` maps locally constant `Z[1/n]`-valued functions to such functions;
- on `Z`, `T` has window-shrinking finite propagation (for the xor pair
  there, window `[a, b]` goes to `[a, b-1]`).

So `Mark(G, A)` is not directly finite for every `|A| >= 2`, including on
`Z`.

**Decoder relaxation is the goal.** `G` is surjunctive on `A` if and only if,
for every automaton `tau` and every `T` in `Mark(G, A)`, `tau^* T = 1`
implies `T tau^* = 1`.

**Kill.** The Gottschalk identity for a strict pair is `tau^* sigma^* = 1`,
with the encoder's Koopman operator `tau^*` on the left. Every
surjunctivity argument whose steps hold in `Mark(G, A)` while using
multiplicativity only of the decoder side dies at `phi psi = 1 => psi phi = 1`
on the xor pair over `Z`. The steps may use:

- linearity, positivity, unitality and equivariance;
- locality and faithfulness;
- preservation of the Bernoulli measure;
- equivariant continuous measure lifts.

The `K_0` class of `1 - xor^* T` vanishes, so no faithful trace or rank
exists on any ring containing this hull. In the 2026-09-12 quantum recovery
audit, the commutative model has `psi` multiplicative and `phi` faithful
UCP, and still `psi phi != id`. So a proof must use determinism
(multiplicativity) of the encoder.

Limits: torsion groups and integral coefficients are open. On locally finite
groups no example of this shape exists. On `Z`, xor has no PCA section with
local randomness.

Proof: route `stochastic-automaton-sections-do-not-force-injectivity-proof`.
