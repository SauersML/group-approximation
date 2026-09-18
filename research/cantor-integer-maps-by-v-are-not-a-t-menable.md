---
rg: 2
id: cantor-integer-maps-by-v-are-not-a-t-menable
kind: claim
title: "The group C(C,Z) ⋊ V does not have the Haagerup property"
distinct_from:
  cantor-integer-maps-by-v-have-haagerup-property: that is the affirmative case Γ = Z of Brothier's Problem B; this is its negation, a negative answer to Problem B
  brin-thompson-2v-is-not-a-t-menable: that denies a-T-menability of 2V; this denies it for the explicit subgroup C(C,Z) ⋊ V ≤ 2V, so it implies that claim but is not known to follow from it
refuted_by:
  - cantor-integer-maps-by-v-have-haagerup-property
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

The group `G = C(C,Z) ⋊ V` admits no proper conditionally negative definite
function. Here `C(C,Z)` is the group of locally constant integer functions on the
Cantor space, and `V` acts by precomposition.

This would be a negative answer to Brothier's Problem B (arXiv:1906.03789v3) with
`Γ = Z`. By `cantor-maps-by-v-embed-in-next-brin-thompson-group`, `G ≤ 2V`, so it
would prove `brin-thompson-2v-is-not-a-t-menable`. It is the negation of
`cantor-integer-maps-by-v-have-haagerup-property`, which is therefore listed as its
refuter.

A sufficient condition is relative property (T) for the pair `(G, C(C,Z))`. By the
artifact §3(f), that is equivalent to the absence of `V`-almost-invariant
(total-variation) probability measures on `Â ∖ {0}` converging to `δ_0`. Here `Â`
is the compact group of finitely additive `T`-valued measures on clopen sets.

## Attempts

- **Localized characters (partial).** Measures on characters with at most `m`
  atoms cannot be almost invariant, because that set of characters is
  `V`-paradoxical. On the complement of a depth-`L` cylinder with `2^L > m`, the
  map `x ↦ 0x` extends to an element of `V` (artifact §3(g)). So any witness to the
  failure of relative (T) must live on non-atomic characters, or on characters with
  unboundedly many atoms. The obstruction is to point-localized measures only.
- **Macroscopic characters (untested obstruction).** Non-atomic candidates, such
  as Gaussian white noise mod 1, fail almost invariance. White noises with
  intensities `m ≠ h_*m` are mutually singular, and `V` preserves no measure that
  gives a clopen set finite positive mass. No proof has been found that every
  non-atomic candidate fails.
- **No distortion to exploit.** Every infinite-order element of `G` is undistorted
  (artifact §3(c), using undistortion of cyclic subgroups of `V`, recalled). So the
  Callard–Salo argument does not even rule out a proper cubical action of `G`.
- **Measure-character and support screen (c-nvhaag, 2026-09-17, ESTABLISHED as
  `cantor-integer-relative-t-witnesses-avoid-measure-characters`).** Any `V`-almost-invariant sequence on
  `Â ∖ {0}` is asymptotically null on four kinds of set:
  - every measure character `f ↦ ∫ f dσ mod 1`. This is a Lusin–Souslin equivariant probability section plus
    halving. It covers all atomic characters, with no bound on the number of atoms, which strengthens §3(g),
    and all Lebesgue densities;
  - every `N_U`, the characters vanishing on `C(U,Z)`;
  - every `Fix(g)` with `g ≠ e`;
  - every countable orbit set with amenable stabilizers.

  So witnesses against relative (T) must be wild, spread-out and essentially free. **Where the screen dies.**
  Haar measure on `Â` is exactly invariant and survives every screen. A proof of relative (T) must therefore
  use `μ_k → δ_0`, and invariance-type obstructions alone cannot finish.
- Not settled.
