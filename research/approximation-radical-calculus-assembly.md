---
rg: 2
id: approximation-radical-calculus-assembly
kind: route
title: Compose the four steps and read off the two extremes
target: approximation-radical-calculus
requires:
  - op-to-hs-shadow-residual-functoriality
  - mf-vs-tracial-radical-strict-gap
  - radical-automorphization
  - single-shadow-word-saturation-compiler
  - arithmetic-single-defect-saturation
  - compression-wreath-five-radicals-coincide
  - alternating-lamp-noncommensurable-family
  - single-finitely-presented-mf-radical-computer
artifacts:
  - GroupApproximation/Endpoint/ApproximationRadicals.lean
  - GroupApproximation/Sofic/RadicalAutomorphization.lean
---

Each step is an established theorem; the content of the composite is that the
output type of one step is the input type of the next, so the cycle closes.

**Produce into renormalize.**  `op-to-hs-shadow-residual-functoriality` makes
`R_{infinity->2}` fully invariant, so a produced word survives every map out of
its source, and `mf-vs-tracial-radical-strict-gap` records that this hypothesis
is strictly weaker than radical membership -- the calculus starts from less
than it delivers.  `radical-automorphization` consumes exactly a normal
subgroup inside a radical and returns the stable kernel, so a produced defect
and a radical-kernel self-surjection compose without further hypotheses.

**Renormalize into saturate.**  `single-shadow-word-saturation-compiler` takes
one nontrivial element of `R_{infinity->2}` in a finitely generated recursively
presented group and returns a 2-generated finitely presented acylindrically
hyperbolic Kazhdan group with full MF radical, every nontrivial quotient
included.  `arithmetic-single-defect-saturation` is the concrete instantiation:
`Gamma(3) x| Z^3`, one Britton-certified compression commutator, and normal
generation of the routed quotient -- no Clifford sign, no finite central
subgroup, no chosen endpoint witness.

**Saturate into separate.**  The saturating endpoint and the exact-radical
criterion are the two readings of the same containment: `Rad(Q) = Q` when the
normal closure fills, and `Rad(G) = N` when the quotient by `N` is visible.
`compression-wreath-five-radicals-coincide` is the separating step carried out
five theories at once, producing one universal visible quotient, and
`alternating-lamp-noncommensurable-family` shows the erased part can carry
enough structure to separate the groups up to commensurability.

**The computational consequence.**
`single-finitely-presented-mf-radical-computer` is what closes the loop back
onto logic: the object the calculus computes has an undecidable internal
equality problem, so "what approximation forgets" is not merely a subgroup but
one whose internal mathematics can be arbitrarily complicated.

Nothing new is proved here.  The route asserts only that these eight results
are the steps of one mechanism and that they compose in the stated order; the
Lean re-export `Endpoint/ApproximationRadicals` is that ordering made
machine-checkable, since every name it lists must resolve.
