---
rg: 2
id: thompson-f-sofic-iff-relator-system-unstable
kind: claim
title: Thompson's F is nonsofic exactly when its two relators are stable in permutations, exactly when their almost-solutions almost commute
distinct_from:
  thompson-v-sofic-iff-not-permutation-stable: that is the same dictionary for the simple group V, where almost-actions are corrected to the trivial one; this is F, whose almost-actions must be corrected through its abelianization Z^2, using Arzhantseva--Paunescu's commutator stability.
  sofic-stable-implies-residually-finite: that is the general principle that a sofic stable group is residually finite, one direction of this claim; this adds the converse for F from its character classification.
  thompson-f-relator-system-stable-in-permutations: that is the open stability question itself; this establishes that it is equivalent to nonsoficity of F.
artifacts:
  - research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md
---

**ESTABLISHED (unreviewed).** Let `F = <a, b | [ab^-1, a^-1ba], [ab^-1, a^-2ba^2]>` be Thompson's group,
and let `d` be the normalized Hamming distance. The following are equivalent.
1. `F` is not sofic.
2. The relator system `{[ab^-1, a^-1ba], [ab^-1, a^-2ba^2]}` is stable in permutations, in the sense
   of Arzhantseva--Păunescu Definition 3.2.
3. **One-commutator form.** For every `epsilon > 0` there is `delta > 0` such that for all `n` and all
   `A, B in Sym(n)` with `d([AB^-1, A^-1BA], id) < delta` and `d([AB^-1, A^-2BA^2], id) < delta`, we have
   `d(AB, BA) < epsilon`.
4. For every almost-homomorphism `phi_n : F -> Sym(k_n)` and every ultrafilter, the fixed-point character
   `g -> lim_omega |Fix phi_n(g)| / k_n` has no regular component.

## What it says

- **The Open problem is necessary.** Arzhantseva--Păunescu (arXiv:1410.2626v2, p. 3) ask whether this
  system is (weakly) stable in permutations, and note that an affirmative answer makes `F` nonsofic.
  By this claim the "stable" form of their question is equivalent to nonsoficity of `F`.
- **Exact solutions commute, and only error can escape.** All finite quotients of `F` are abelian, so
  exact solutions in `Sym(n)` are exactly the commuting pairs. The positive side needs `delta`-solutions
  whose commutator stays a fixed proportion away from the identity.
- **For V.** `F <= V`, so (3) makes `V` nonsofic: route `thompson-v-not-sofic-from-f-not-sofic`.
- **Mechanism.** The fixed-point character is `t tau_reg + (1-t) chi_ab`
  (`thompson-f-character-simplex`). Tensor amplification together with a `Z^2`-torus factor turns
  `t > 0` into soficity. When `t = 0` the generators almost commute, and Arzhantseva--Păunescu's commutator
  stability (`almost-commuting-permutations-are-near-commuting`) supplies the exact commuting solutions.

Derivation: `thompson-f-sofic-iff-relator-system-unstable-proof`.
