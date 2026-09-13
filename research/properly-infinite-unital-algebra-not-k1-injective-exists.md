---
rg: 2
id: properly-infinite-unital-algebra-not-k1-injective-exists
kind: claim
title: Some properly infinite unital C*-algebra is not K1-injective (negation of STW LXI)
distinct_from:
  stw99-problem-lxi-properly-infinite-k1-injective: that root asserts K1-injectivity for all properly infinite unital algebras; this is its negation, the target for counterexample routes.
---

There is a unital properly infinite C\*-algebra `A` and a unitary `u ∈ U(A)` with `[u] = 0` in `K_1(A)`
and `u ∉ U_0(A)`. By Blanchard--Rohde--Rordam Theorem 5.5 this happens iff the full free product
`O_∞ * O_∞` is not K1-injective.

## Attempts

- Blanchard's arXiv:1606.04773v1 claims `T_2 *_C T_2` as such an algebra. The non-null-homotopy step
  has a covariance defect, recorded in the LXI root's firewall.
- Free envelope `A_LIX * T_2` of the simple AH witness: its stable nullness is proved, its non-nullness
  is not. The `stw61-*` maximal-commutator theorems exclude large families of projections from the
  strict BRR criterion, but they cannot prove non-nullness.
- Tensoring with properly infinite algebras, corners whose complement dominates the corner, and
  quotients all kill finite witnesses (artifact `stw61-free-envelope-compression-attack-2026-09-05`).
- Pimsner--Toeplitz fields of `O_∞` over the Hilbert cube: properly infinite
  (`dd-toeplitz-algebra-is-properly-infinite`), so they are not a source.
- Reduction (route `lxi-negation-from-o2-multiplier-ideal`): it suffices to find a non-unital `I` with
  a unital `O_2` in `M(I)` whose unitization is not K1-injective. Euler-class protection of the witness
  is impossible there (`euler-class-protection-fails-for-o2-self-similar-modules`).
- Quantitative form: a family of properly infinite algebras whose unstable exponential length
  diverges while the stabilized length stays bounded (`properly-infinite-unstable-length-uniformly-bounded`).
