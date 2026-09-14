---
rg: 2
id: amplified-algebraic-roots-in-characteristic-zero
kind: claim
title: Every nonsingular equation with matrix constants over an algebraically closed field of characteristic zero has approximate roots after amplification
distinct_from:
  amplified-algebraic-roots-for-nonsingular-equations: that quantified over all algebraically closed fields and is refuted in odd characteristic; this is its characteristic-zero case.
  amplified-roots-fail-in-odd-characteristic: that is the odd-characteristic counterexample; this is the case the counterexample does not reach.
artifacts:
  - research/artifacts/ideas-nonhyperlinear-2026-09-13.md
---

**OPEN.** For every algebraically closed field `L` of characteristic `0`, every
`n >= 1`, every tuple `a` in `GL_n(L)^k`, every `w` in `F_k * <t>` with nonzero
exponent sum in `t`, and every `epsilon > 0`, there are `r >= 1` and `T` in
`GL_{nr}(L)` with `rho(w(T ; a (x) 1_r) - 1) <= epsilon`.

This is `ARR(L)` of `linear-sofic-kl-from-amplified-algebraic-roots` in
characteristic 0.
- **Why the odd-characteristic counterexample doesn't transfer.** It uses the
  Frobenius identity `(s-1)^p = s^p - 1`, which turns a unipotent constant
  into a rank profile for `s - 1`.
- **Known.** Over `C`, unitary constants have exact roots with `r = 1`, by the
  Gerstenhaber--Rothaus degree argument recorded in
  `kervaire-laudenbach-holds-for-hyperlinear`.
- **Open.** Constants that are not unitarizable, for example ones with
  unipotent Jordan blocks.
