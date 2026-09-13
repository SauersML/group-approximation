---
rg: 2
id: free-group-doubles-over-any-subgroup-are-sofic
kind: claim
title: Every symmetric double of a countable free group over any subgroup is sofic, and every subgroup inclusion of free group factors is RE/C
distinct_from:
  sofic-coset-action-makes-amalgam-double-sofic: that is the general theorem with a sofic-coset-action hypothesis; this is the free-actor case where the hypothesis holds for every subgroup, including normal subgroups with nonsofic or Kazhdan quotient
  mihailova-coset-wreath-sofic-action-boundary: that shows the free restriction of the Mihailova coset action is sofic and so cannot test the quotient; this upgrades that free restriction to soficity of the double E *_N E and scalar relative embeddability of L(N) in L(E)
  waldhausen-free-double-whitehead-space-contractible: that is about Whitehead spaces of free-group doubles; this is about soficity and relative embeddability, with no K-theoretic content
---

Let `F` be a countable free group and `Γ ≤ F` an arbitrary subgroup: of any
rank, normal or not, finitely generated or not. Then:

1. The symmetric amalgamated double `D = F *_Γ F` is sofic.
2. `L(F) *_{L(Γ)} L(F) = L(D)` is Connes embeddable.
3. The inclusion `L(Γ) ⊂ L(F)` is relatively embeddable over the scalars
   (`RE/C`).

**What is new here, and what is classical.**
- For finitely generated `Γ`, item 1 also follows from a classical
  criterion, which was not re-verified here. M. Hall's theorem makes `Γ`
  separable in `F`, and a double of a residually finite group over a
  separable subgroup is residually finite.
- For infinitely generated `Γ`, the double need not be residually finite, and
  item 1 needs the action theorem. A normal `Γ` with nonsofic quotient
  `Q = F/Γ` gives a sofic group `D`: the fold kernel is free and `D` maps onto
  `Q * Q`, which is nonsofic.
- The novelty of the infinitely generated case was **not checked** against
  the literature.

**Consequence for the Mihailova data.** Take `E = F_m < SL_3(Z)`,
`π : E → Q` and `N = ker π`, as in
`mihailova-coset-wreath-sofic-action-boundary`. Then `E *_N E` is sofic and
`L(N) ⊂ L(E)` is `RE/C`, whatever `Q` is (finitely presented, Kazhdan,
nonsofic). By `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`,
the Mihailova wreath `W_N` is hyperlinear exactly when `L(N) ⊂ L(SL_3(Z))`
is `RE/C`. So any obstruction must live in the ambient step from `L(E)` to
`L(SL_3(Z))`, not in the free step from `L(N)` to `L(E)`.

DERIVATION
free-group-doubles-over-any-subgroup-are-sofic-proof
