---
rg: 2
id: kazhdan-hyperbolic-hs-stability-kills-hyperlinearity
kind: claim
title: A flexibly HS-stable Kazhdan hyperbolic group with positive second Betti number has a non-hyperlinear hyperbolic finite central extension
distinct_from:
  hs-stability-forces-nonhyperlinear-central-extension: that is the Dogon--Vigdorovich theorem for (T;FD) groups admitting an integral central extension with finite abelianization; this specializes it to hyperbolic Kazhdan groups, supplies the extension from b_2 >= 1, and records that the output is itself hyperbolic
  random-complex-cocycle-cheeger-beats-triangle-count: that is the permutation-side hypothesis of Chapman--Peled on random complexes; this is a unitary-side stability hypothesis on any single hyperbolic Kazhdan group, with no randomness and no finite-quotient content
---

**ESTABLISHED.** Let `Γ` be a word-hyperbolic group with property (T) and
`b_2(Γ; Q) >= 1`. If `Γ` is flexibly Hilbert--Schmidt stable, then some finite
central extension

```text
1 --> Z/N --> Γ_N --> Γ --> 1
```

is not hyperlinear, and `Γ_N` is word-hyperbolic. So `Γ_N` is a non-hyperlinear
hyperbolic group. It is therefore a nonsofic hyperbolic group, and in particular
not residually finite.

**Contrapositive, as a no-go.** Suppose every hyperbolic group were hyperlinear,
which the Gromov question expects. Then no hyperbolic Kazhdan group with
`b_2 >= 1` would be flexibly Hilbert--Schmidt stable.

## Why this is a second mechanism for the root

Chapman--Peled attach Dogon's 2023 theorem to random complexes, and say in their
Remark 1.2 and footnote 5 that the non-hyperlinear groups it yields are not known
to be hyperbolic. That was the infinite cyclic extension. Dogon--Vigdorovich
(arXiv:2506.20843) instead kill a *finite* quotient of that extension. A finite
central extension of a hyperbolic group is quasi-isometric to it, hence hyperbolic.
So the unitary stability route now lands squarely in `nonsofic-hyperbolic-group`,
with a hypothesis about one hyperbolic Kazhdan group rather than about finite
quotients.

DERIVATION
kazhdan-hyperbolic-hs-stability-kills-hyperlinearity-proof
