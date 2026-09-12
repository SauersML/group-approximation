---
rg: 2
id: ternary-anti-central-unit-class-is-nonpositive
kind: claim
title: Some positive multiple of the unit class of the ternary anti-central summand is nonpositive in K_0
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the unstable corner equation, which implies this condition with k = 1; this is the stable K_0 condition, which allows stabilization and an arbitrary projective complement and still suffices for a counterexample.
  leavitt-group-algebra-not-stably-finite: that is failure of stable finiteness for the binary group algebra over F_2; this is a K_0 positivity failure on the anti-central summand of the ternary group algebra, strictly stronger than non-stable-finiteness of that summand.
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

**OPEN.** Let `S_- = eps_- F_3[L_(F_3)(1,2)^x]`. Exhibit `k >= 1`, `r >= 0` and a finitely generated
projective `Q` with

    S_-^r ~= S_-^r (+) S_-^k (+) Q,

that is, `k[eps_-] <= 0` in `K_0(S_-)`.

**Why it matters.**
- *It refutes Gottschalk.* By `nonpositive-unit-class-refutes-ternary-surjunctivity`, it gives a
  one-sided pair in `M_r(F_3[G_3])` and hence a strict automaton on `G_3`.
- *It is exactly what no state can see.* By `anti-central-state-obstruction-equals-stable-finiteness`,
  a state on `(K_0(S_-), [eps_-])` exists iff this claim fails.
- *It is weaker than the corner equation.* The corner equation implies it with `k = 1`
  (`anti-invariant-corner-gives-nonpositive-unit-class`).

## Attempts

- *Image.* In `R = L_(F_3)(1,2)` the isomorphism holds trivially, since `R ~= R (+) R`. So this is a
  lifting problem at matrix size, with more room than the unstable corner equation.
- *Obstructions ruled out.*
  - Every additive invariant is inert, because `[eps_-] = 2[e_-]` (Theorem B(i) of the artifact).
  - `S_-` has no finite-dimensional images
    (`ternary-anti-central-summand-has-no-finite-dimensional-images`).
  - The only possible obstruction is a state, and its natural source, a rank function from an
    `F_3`-linear sofic approximation of `G_3` with `z` acting as `-1`, is the open gate. Property (T)
    gives no rank rounding over finite fields.
- *Where it dies today.* No matrix-size lift of `R ~= R (+) R` to `S_-` has been built, and no state on
  `K_0(S_-)` is known.
