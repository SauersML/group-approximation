---
rg: 2
id: twice-punctured-torus-mcg-is-continuous-automatic
kind: claim
title: The mapping class group of the twice-punctured torus is continuous automatic, given the Birman--Hilden identification with the five-punctured sphere
distinct_from:
  low-complexity-mapping-class-groups-are-continuous-automatic: that covers punctured spheres, genus one with at most one puncture, and closed genus two using only standard facts; this adds S_{1,2}, which needs one more recalled identification.
  mapping-class-groups-are-continuous-automatic: that is BBCMP Question 1.16 for all finite-type surfaces; this is its smallest case beyond the low-complexity list.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**OPEN: the proof is complete except for the recalled input (M5) below, which was not
read at source.** Lane proof, not reviewed.

**Statement.** `Mod(S_{1,2})` is continuous automatic, in the sense of
Belk--Bleak--Chatterji--Matucci--Perego (BBCMP, preliminary version).

**(M5), recalled.**
- `S_{1,2}` has a hyperelliptic involution `ι` that exchanges the two punctures. It is
  central in `Mod(S_{1,2})` and has order 2.
- `Mod(S_{1,2})/⟨ι⟩` is isomorphic to a finite-index subgroup of `Mod(S_{0,5})`, namely the
  stabilizer of the image of the punctures. This is Birman--Hilden for the double cover
  `S_{1,2} → S_{0,5}` branched at four of the marked points.
- **Evidence.** Luo, arXiv:math/9904020 (abstract, read) singles out "the 2-holed torus"
  as the one surface whose curve-complex automorphisms are not all induced by
  homeomorphisms, as this identification predicts. Korkmaz (1999) is usually cited for
  the identification. Neither the Birman--Hilden statement for `S_{1,2}` nor Korkmaz was
  read.

**Proof, given (M5).**
- `Mod(S_{1,2})` has a torsion-free subgroup `Γ` of finite index (level-3 congruence
  subgroup). Then `Γ ∩ ⟨ι⟩ = 1`, so `Γ` maps isomorphically onto a finite-index subgroup of
  `Mod(S_{0,5})`.
- So `Mod(S_{1,2})` is commensurable with `Mod(S_{0,5})`.
- `Mod(S_{0,5})` is continuous automatic by
  `low-complexity-mapping-class-groups-are-continuous-automatic`.
- BBCMP Proposition 1.4(2), used as printed, finishes the proof.
