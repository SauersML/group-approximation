---
rg: 2
id: affine-congruence-source-is-kazhdan
kind: claim
title: The affine congruence compression source is Kazhdan, not merely bare
distinct_from:
  concrete-compression-source: that claim is deliberately the BARE datum and states in terms that property (T) is not involved; this one supplies the (T) certificate for the level-three source, which is the hypothesis the normal-Kazhdan detector actually consumes.
  literal-kazhdan-clifford-inputs: that claim is about the six-generator affine BASE displayed in the manuscript; this one is about its torsion-free level-three subgroup, which is the group the torsion-free program compresses.
  defect-forces-proper-self-embedding: that claim is the structural constraint saying which cores can carry a nontrivial defect at all; this one exhibits a classical arithmetic group that meets the constraint.
artifacts:
  - GroupApproximation/Sofic/LiteralAffineCongruenceKazhdan.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceTorsionFree.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
  - GroupApproximation/Sofic/LiteralAffineFreeProductSource.lean
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
---

The level-three affine congruence group

```text
P = Gamma(3) ltimes Z^3,      Gamma(3) = ker(SL_3(Z) -> SL_3(Z/3)),
```

is finitely presented, torsion-free **and has property (T)**, and the
translation dilation `alpha(g,v) = (g, m v)` is for every `m >= 2` an injective
endomorphism of `P` whose image `Gamma(3) ltimes m Z^3` has index `m^3`, with
`p_0 = (1, e_1)` outside it.

Consequently the bare datum of `concrete-compression-source` upgrades to a full
`KazhdanCompressionCore`: source Kazhdan, stable letter compressing properly,
centralizing witness, Britton-nontrivial marked commutator, inside a
torsion-free finitely presented ambient.

**Why this is the load-bearing addition.**  `concrete-compression-source` is
stated without (T) on purpose — the routing architecture creates all obstruction
downstream.  But the detector does not: `defect-forces-proper-self-embedding`
records, as a correction dated 2026-08-21, that the core's (T) field is *not*
vestigial, because the root-capture step of the kill theorem opens by extracting
a spectral gap from property (T) of the **base**.  A core over an amenable base
proves nothing.  So the source must be Kazhdan, and this claim says the affine
congruence source already is.

**It answers the sharp source demand.**  That same node isolates the surviving
demand as *a property-(T) group with a proper self-embedding, with a
centralizing root and nontrivial marked commutator, realized inside a
torsion-free finitely presented ambient*, and concludes that no off-the-shelf
classical group qualifies, because higher-rank lattices and torsion-free
hyperbolic (T) groups are co-Hopfian.  `P` qualifies and is off the shelf: it
is not a lattice in a semisimple group, the dilation moves only the translation
factor, and the arithmetic linear part — the part rigidity makes co-Hopfian —
is untouched.  The Fournier--Facio universal-group machinery is therefore not
needed for the source.

**LEAN STATUS.**  Property (T) is
`LiteralAffineCongruenceBase.p_hasKazhdanPropertyT` (finite-index permanence
applied to the certified affine base), finite presentation is
`p_isFinitelyPresented`, torsion-freeness is
`LiteralAffineCongruenceTorsionFree.p_isPowerTorsionFree`, and the compression
data are `LiteralAffineCongruenceSource.compression`, `compression_injective`,
`omitted`, `omitted_not_mem_range`.  The repository's certified instance takes
`m = 2`; nothing downstream distinguishes the modulus.
