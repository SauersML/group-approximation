---
rg: 2
id: f9-hadamard-spectral-idempotent-is-full
kind: claim
title: The F_9 Hadamard spectral idempotent is full in the anti-central summand of the ternary Leavitt group algebra
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that asks for c e_- b = eps_- with the F_3 swap idempotent e_- = 2eps_-(1 + [w]); this asks for c f_+ b = eps_- with the non-monomial F_9 spectral idempotent of the Hadamard unit, a different half idempotent whose fullness also yields the Cohn family.
artifacts:
  - research/artifacts/f9-hadamard-spectral-cohn-attempt-2026-09-12.md
---

**OPEN.** With `f_+ = 2(1_- + i[h])` as in `f9-hadamard-spectral-idempotents-are-half-idempotents`,
exhibit `b, c` in `S_-^(9) = eps_- F_9[L_(F_3)(1,2)^x]` with `c f_+ b = 1_-`. By part 4 of that claim
and `ternary-anti-central-cohn-family-over-f9`, this refutes Gottschalk's conjecture on
`L_(F_3)(1,2)^x`.

## Attempts

- *Why try it.* `f_+` is non-monomial already at depth one, so its support escapes the signed Thompson
  crossed product, whose Haar measure forbids honest compressions
  (`odd-measure-space-has-no-honest-thompson-compression`).
- *Constants alone.* Dead. Every constant unit lies in a locally finite subgroup, and a family
  supported on a finite subgroup lives in a finite-dimensional algebra, which is directly finite.
- *State filter.* Part 5 of the half-idempotent claim: the support subgroup must have no
  characteristic-three rank model moving `z`.
- *Where it dies today.* No finitely supported witness is known. See the artifact for the collapse
  audit of spectral monomial lifts.
- *Equivalent to the swap corner (w4-hadamard-f3, 2026-09-12).* `f_+ = W e_- W^(-1)` for the unit
  `W = v[c]` of `hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent`: `c` is the constant
  involution `[[-1,0],[1,1]]` carrying `(wd, d)` to `(h, u)`, and `v` joins two rank-one idempotents of the
  dihedral copy of `M_2(F_9)`. So this claim is equivalent to `ternary-anti-invariant-swap-corner-is-full`
  (route `f9-hadamard-fullness-from-swap-corner-fullness` plus the existing chain). The surviving idea of the
  collapse audit, that `h` in the support escapes the signed Thompson crossed product, is the escape the
  swap corner already makes through `q_[0] = [h] e_- [h]^(-1)`. Designs translate with supports multiplied by
  `<h, u> c`; the state filter is the swap filter transported by `[c]`. Section 1 of
  `research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md`.
