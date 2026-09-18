---
rg: 2
id: aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups
kind: claim
title: Every Aut(F_n) quasi-isometrically embeds in a finitely presented simple group, and the BFFHZ host distorts a subgroup of Aut(F_n) exactly as Aut(F_n) does
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that is the BFFHZ embedding of Aut(F_n) in a finitely presented simple twisted Brin--Thompson group; this shows that the same embedding is a quasi-isometric embedding.
  hyperbolic-groups-undistortedly-embed-in-fp-simple-groups: that treats hyperbolic groups through the BBMZ horofunction host; this treats Aut(F_n), which is not hyperbolic for n >= 2, through the BFFHZ relative-automorphism host.
  twisted-brin-thompson-groups-quasi-retract-onto-acting-group: that is the Belk--Zaremsky undistortion of the acting group in SV_G; this adds the retraction of the acting group onto Aut(F_n).
---

**ESTABLISHED** through `aut-free-qi-embedding-in-twisted-brin-thompson-proof` (a lane proof, not
independently reviewed). The argument is two lines on top of BFFHZ and Belk--Zaremsky, and no priority is
claimed. BFFHZ (arXiv:2503.21882v2) does not discuss distortion.

**Statement.** Let `n >= 1`. Let `V` be Thompson's group, `Γ = Aut_V(V * F_n)` the automorphisms of
`V * F_n` that restrict to the identity on `V`, and `S = Hom_V(V * F_n, V)`. Let `SV_Γ` be the finitely
presented simple twisted Brin--Thompson group of BFFHZ Theorem A (`aut-free-groups-satisfy-permutational-boone-higman`).
1. The BFFHZ embedding `Aut(F_n) → Γ → SV_Γ`, with `α ↦ id_V * α`, is a quasi-isometric embedding of word
   metrics. So `Aut(F_n)` is undistorted in a finitely presented simple group.
2. More precisely, `Aut(F_n)` is a retract of `Γ`, and `Γ` is a quasi-retract of `SV_Γ`. So for every
   finitely generated `H <= Aut(F_n)`, the distortion function of `H` in `SV_Γ` is equivalent to its
   distortion function in `Aut(F_n)`. In particular, `H` is undistorted in `SV_Γ` if and only if it is
   undistorted in `Aut(F_n)`.

**What this gives for Zaremsky's list.** Zaremsky (arXiv:2201.00711v1, TeX l.495–497; node
`hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups`) asks whether braid groups and mapping
class groups embed "(quasi-isometrically?)" in finitely presented simple groups. BFFHZ Corollary B reaches
braid groups and mapping class groups of non-closed surfaces by embedding them in some `Aut(F_m)`. By part
2, the BFFHZ host embeds such a group quasi-isometrically if and only if its chosen embedding in `Aut(F_m)`
is undistorted. This lane did not settle that.
- **Braid groups.** `B_n <= Aut(F_n)` is Artin's embedding. Composing with the injective homomorphism
  `Aut(F_n) → Out(F_n * <t>)`, `φ ↦ [φ * id_t]`, gives the Dehn--Nielsen--Baer image of `B_n` in
  `Map(S_{0,n+2})`. The boundary of the disk is capped there by a twice-punctured disk. That homomorphism is
  Lipschitz, so undistortion of `B_n` in `Out(F_{n+1})` would suffice. Hamenstädt--Hensel
  (arXiv:1109.2687, Theorem 3) prove the analogous statement only for one puncture: `Map(S_{g,1})` is a
  coarse Lipschitz retract of `Out(F_{2g})`. The lane found no statement for several punctures, and none
  for `Aut(F_n)`.
- **Out(F_n), closed-surface mapping class groups, CAT(0) groups.** Boone--Higman itself is open for them,
  so this route says nothing.

**Scope.** Parts 1 and 2 use only the existence of the BFFHZ host and the Belk--Zaremsky quasi-retraction.
The high transitivity of the action is not used.
