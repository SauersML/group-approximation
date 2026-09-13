---
rg: 2
id: fp-simple-kac-moody-pbh-via-mif-and-theorem-c
kind: route
title: Kac--Moody permutational Boone--Higman from Rybak's MIF theorem and BFFHZ Theorem C
target: fp-simple-kac-moody-lattices-satisfy-pbh
requires:
  - fp-simple-kac-moody-lattices-are-mif
  - fp-simple-highly-transitive-groups-satisfy-pbh
---

**Proof.** `G(F)` is finitely presented and simple, and it is MIF by
`fp-simple-kac-moody-lattices-are-mif`. BFFHZ Theorem C, imported as
`fp-simple-highly-transitive-groups-satisfy-pbh`, states: "In particular, every
finitely presented simple group that is highly transitive, or more generally MIF,
satisfies the permutational Boone–Higman conjecture, as does every subgroup
thereof." Applying it to `G(F)` gives the claim. ∎
