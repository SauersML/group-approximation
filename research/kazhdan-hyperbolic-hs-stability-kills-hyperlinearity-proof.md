---
rg: 2
id: kazhdan-hyperbolic-hs-stability-kills-hyperlinearity-proof
kind: route
title: Integral extension from b_2, Dogon--Vigdorovich truncation, quasi-isometry invariance of hyperbolicity
target: kazhdan-hyperbolic-hs-stability-kills-hyperlinearity
requires: [hs-stability-forces-nonhyperlinear-central-extension, sofic-implies-hyperlinear]
---

## Direct proof

Let `Γ` be hyperbolic and Kazhdan with `b_2(Γ;Q) >= 1`, and flexibly
Hilbert--Schmidt stable. Dogon--Vigdorovich's "Hilbert--Schmidt stable" is the
flexible notion, per the transcription note in the required claim.

1. **(T;FD).** Property (T) gives a uniform Kazhdan constant for every unitary
   representation without invariant vectors, in particular the finite-dimensional
   ones. So `Γ` has Lubotzky--Zimmer's property (T;FD).
2. **An integral central extension with finite abelianization.** `Γ` is finitely
   presented (hyperbolic) and `H_1(Γ;Z)` is finite (T). `H_2(Γ;Z)` is finitely
   generated of rank `b_2 >= 1`. The universal coefficient sequence makes
   `H^2(Γ;Z) -> Hom(H_2(Γ;Z), Z)` onto, so there is `c` whose evaluation `φ`
   is nonzero. Let `1 -> Z -> Γ~ -> Γ -> 1` be the central extension of class `c`.
   Its five-term exact sequence
   `H_2(Γ;Z) --±φ--> Z -> H_1(Γ~;Z) -> H_1(Γ;Z) -> 0`
   exhibits `H_1(Γ~)` as an extension of the finite group `H_1(Γ)` by
   `Z/φ(H_2(Γ))`. The latter is finite because `φ != 0`. So `Γ~` has finite
   abelianization.
3. **Truncation.** By `hs-stability-forces-nonhyperlinear-central-extension`,
   there is `N` such that `Γ_N = Γ~/(N·Z)` is not hyperlinear.
4. **Hyperbolicity.** `Γ_N -> Γ` is onto with finite kernel `Z/N`, so the two
   groups are quasi-isometric. Word-hyperbolicity is a quasi-isometry invariant of
   finitely generated groups, so `Γ_N` is hyperbolic.
5. **Nonsoficity.** Sofic groups are hyperlinear (`sofic-implies-hyperlinear`),
   so `Γ_N` is nonsofic, and residually finite groups are sofic.

∎
