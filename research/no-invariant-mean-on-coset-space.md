---
rg: 2
id: no-invariant-mean-on-coset-space
kind: claim
title: A Kazhdan group has no invariant mean on an infinite-index coset space
invalidates: [induced-charge-extension]
distinct_from:
  coordinate-action-not-sofic: that says the coset action admits no finite permutation approximation and is imported by citation; this says it admits no invariant finitely additive measure at all, and is proved here from property (T)
  finite-quotient-blindness: that is about exact finite quotients normalizing the image of Γ; this is about means on the coset space, with no quotient in sight
  haagerup-t-exclusion: that excludes Haagerup carriers because they contain no diffuse (T) subalgebra; this excludes invariant means because (T) upgrades almost invariant vectors to invariant ones
artifacts:
  - notes/TRUE_CHARGE_EXTENSION_NEEDS_COAMENABILITY.md
---

Let `G` have property (T) and `Γ ≤ G` have infinite index. Then there is no
`G`-invariant finitely additive probability measure on `G/Γ`: `Γ` is not
co-amenable in `G`.

Proof (Proposition 1 of the artifact): a mean gives, via Day's trick, finitely
supported probability densities `f_i` with `‖g·f_i − f_i‖₁ → 0`; then
`ξ_i = f_i^{1/2}` are almost invariant unit vectors in `ℓ²(G/Γ)` by
`|√a − √b|² ≤ |a − b|`; property (T) produces a nonzero invariant vector, which
by transitivity is a constant function, and a nonzero constant is square
summable only if `G/Γ` is finite.

This is `notes/OBSTRUCTIONS.md` §3's "`G ↷ G/Γ` has no Følner sets" in the form
the charge language needs, and it is what kills `induced-charge-extension`.

## Why it matters beyond that route

It settles, negatively, the asymmetry that motivated the Kahl–Schneider lane.
The hope was that an invariant charge might extend over the compressors where
Connes embeddability does not, since extending finitely additive measures is
Hahn–Banach's home ground while extending CE across an amalgamated free product
over a nonamenable base is a named open problem (Gao–Junge). The comparison was
mis-drawn: Hahn–Banach extends a charge from a smaller family of sets to a
larger one *with the same invariance group*, and does not extend an invariant
charge along a group inclusion. On this comparison the charge side is strictly
worse off than the algebra side, because this claim is a theorem while
Gao–Junge Problem 1 is open.
