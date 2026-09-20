---
rg: 2
id: thompson-f-trace-spread-caps-the-census-ratio
kind: claim
title: Unitary pairs whose traces on finitely many nontrivial F' words are unequal have commutator-to-relator ratio bounded in every dimension
distinct_from:
  thompson-f-hyperlinear-iff-relator-system-hs-unstable: that proves the equivalence of nonhyperlinearity with uniform relator stability; this bounds the ratio uniformly on the explicit subclass of pairs whose trace vector on a finite S in F' misses the constant segment, so any divergent census family must become trace-consistent.
  thompson-f-commutator-bound-holds-in-each-fixed-dimension: that bounds the ratio in each fixed dimension by a constant growing with n; this is dimension-free but restricted to pairs with trace spread at least eta, and it shows the fixed-threshold census is bounded above threshold 2.
  thompson-f-character-simplex: that classifies the characters; this is its quantitative matrix consequence via ultraproducts.
artifacts:
  - research/artifacts/thompson-f-census-trace-spread-2026-09-17.md
---

**Statement.** Let `F = <a, b | R_1, R_2>` with `R_1 = [ab^-1, a^-1ba]` and `R_2 = [ab^-1, a^-2ba^2]`, and let `c = [a,b]`.
Write `e(X) = ||X - I||_2^2` in normalized Hilbert--Schmidt norm.

Let `S` be a finite subset of `F' \ {e}`. For a unitary pair `(U, W)`, the spread `sigma_S(U,W)` is the sup-norm
distance from the trace vector `(tr w(U,W))_{w in S}` to the segment `{(s, ..., s) : 0 <= s <= 1}`.

1. **Spread lemma.** For each `eta > 0` there is `delta(S, eta) > 0` such that every unitary pair of any size with
   `sigma_S >= eta` has `max_i e(R_i) >= delta(S, eta)`. Hence `e(c) / max_i e(R_i) <= 4 / delta(S, eta)`, uniformly
   in the dimension.
2. **Above threshold 2.** For every `tau > 2`, `inf_n inf { max_i e(R_i) : (U, W) in U(n)^2, e(c) >= tau } > 0`,
   whether or not `F` is hyperlinear.
3. **Shape of divergence.** If the ratio `e(c) / max_i e(R_i)` tends to infinity along a sequence of pairs, then
   `sigma_S -> 0` along that sequence for every finite `S` in `F' \ {e}`. In particular all nontrivial `F'` words
   acquire asymptotically equal, real, non-negative traces.

The constants are not effective. Item 3 is an exact criterion that census evidence for hyperlinearity of `F` must
meet: ratio growth along a family whose spread on one fixed `S` stays at least `eta` is capped at `4/delta(S, eta)`.
The claim `thompson-f-census-witnesses-have-frozen-trace-spread` records that the best known census witnesses are
in such a family.

Derivation: `thompson-f-trace-spread-caps-the-census-ratio-proof`.
