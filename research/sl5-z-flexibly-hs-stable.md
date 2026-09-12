---
rg: 2
id: sl5-z-flexibly-hs-stable
kind: claim
title: SL5 over the integers is flexibly Hilbert-Schmidt stable
artifacts:
  - research/artifacts/sep7-padded-heat-linear-seed-self-improvement-2026-09-07.md
distinct_from:
  sln-z-flexibly-hs-stable: that asks for some rank at least three; this fixes rank five, which is needed for the specified universal quotient and its quantitative spectral seeds.
  padded-heat-equates-linear-logarithmic-schreier-seeds: that is an established equivalence between open properties; this is the open truth of its specific rank-five stability assertion.
---

Every inverse-compatible asymptotic unitary representation of SL_5(Z)
admits exact representations after padding by a vanishing relative
dimension, with normalized-HS generator errors tending to zero.

This assertion is open. The existing claim that some SL_n(Z), n>=3,
is flexibly stable would not by itself imply this rank-five assertion.
The padded heat equivalence identifies this assertion with the uniform
linear and logarithmic first-vector estimates; it proves none of those
assertions without an additional input.

## Attempts

The September 7 padded-heat audit shows that a supplied coarse exact
comparison of dimension at most twice the input produces a linear
first-vector estimate, even if known flexible corrections converge
arbitrarily slowly. Hence compressed exact representations and slow
correctable sequences cannot furnish a counterexample. The argument
still needs that comparison for arbitrary small-defect tuples; neither
the universal finite host nor the coset-wreath hyperlinearity
equivalence supplies it.
