---
rg: 2
id: bernoulli-witness-information-is-bounded-by-code-reads
kind: claim
title: The information a Bernoulli configuration carries about one site is at most the entropy of the codewords that read it
distinct_from:
  transport-identity-gives-reciprocal-memory-entropy-bound: that bounds the site entropy of an injective automaton's output by its decoder memory size; this bounds the information finite codewords of an arbitrary code carry about one input site, the quantity in the finitary Rokhlin witness.
  bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup: that localizes a deficit witness to a subgroup; this bounds its value by the number of codewords reading the special site.
artifacts:
  - research/artifacts/rokhlin-window-localization-and-read-bound-2026-09-12.md
---

For every countable group `G`, `|A| = q >= 2`, and configuration `(k, E, F, psi)` as in
`bernoulli-rokhlin-deficit-has-a-finitary-witness`, put `m = |F ∩ E^-1| <= |E|`, the number of
codewords reading the site `1`. Then

    I( x(1) ; y_F ) <= min{ k log q , m H(psi(x|_E)) },

and hence `Phi >= log q / m` when `m >= 1` (and `Phi >= log q` when `m = 0`).

**Consequence.** Let `n >= 1` be an integer. A configuration with `Phi < log q / n` has `m > n`,
so `|E| > n`, and `H(psi) < k log q / n`. Indeed `m = 0` would give `Phi >= log q`, so `m >= 1`.
Then `log q / m <= Phi < log q / n` gives `m > n`, and `H(psi)/k <= Phi` gives the entropy bound.

The proof is the chain rule plus subadditivity: codewords not reading `1` are independent of
`x(1)`, and each codeword that does has the law of `psi(x|_E)`. It uses no group structure beyond
left cancellation of reads, so it gives no uniform lower bound on Rokhlin entropy. Section 2 of
the artifact.

**ESTABLISHED 2026-09-12** by [[bernoulli-witness-read-degree-bound-proof]].
