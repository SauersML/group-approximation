---
rg: 2
id: undistorted-type-a-class-closure-and-qi-boone-higman
kind: claim
title: Groups undistorted in a type (A) actor quasi-isometrically embed in finitely presented simple groups, and this class is closed under products and finite extensions and contains punctured-sphere and genus-two mapping class groups
distinct_from:
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure of B_A (embedding in a type (A) actor, no geometry) under products and finite-index overgroups; this is the same closure for undistorted embeddings, with the quasi-isometric Boone--Higman consequence.
  braid-groups-quasi-isometrically-embed-in-fp-simple-groups: that treats braid groups and bordered mapping class groups one at a time; this packages the undistorted class and adds its closure, which reaches punctured-sphere and closed genus-two mapping class groups.
  hyperbolic-groups-lie-in-the-permutational-class: that puts hyperbolic groups in B_A through type (A) rational similarity groups; this uses the undistortion of the same chain.
---

**ESTABLISHED** through `undistorted-type-a-class-closure-proof`. This is a lane proof, not independently
reviewed. No priority is claimed. The closure arguments are Zaremsky's (arXiv:2405.18354, Propositions 5.5 and
5.6), with metrics tracked.

**Definition.** `QB_A` is the class of finitely generated groups `G` with an injective homomorphism `G → E`
that is a quasi-isometric embedding, where `E` admits an action of type (A). Type (A) means: faithful,
`E` finitely presented, point stabilizers finitely generated, finitely many orbits of two-element subsets.

**Statement.**
1. **QI Boone–Higman.** Every `G ∈ QB_A` quasi-isometrically embeds in the finitely presented simple group `SV_E`.
2. **Closure.** `QB_A` is closed under:
   - finitely generated undistorted subgroups;
   - finite direct products;
   - finite-index overgroups, hence under commensurability.
3. **Members.**
   - Hyperbolic groups.
   - `Aut(F_n)`, and every group undistorted in some `Aut(F_m)`. This includes `B_n`, `Mod(S_g^b)` with
     `b >= 1`, and the Artin groups of type `B_n`.
4. **New consequences of 2 and 3.**
   - **Punctured spheres.** `Mod(S_{0,m})` is in `QB_A` for every `m`: its pure subgroup is a direct factor
     of the pure braid group `PB_{m−1}`.
   - **Genus two.** The closed genus-two mapping class group `Mod(S_2)` is in `QB_A`. By residual finiteness it
     has a finite-index subgroup that maps isomorphically onto a finite-index subgroup of `Mod(S_{0,6})`.
   - **Dihedral Artin groups.** The Artin groups of type `I_2(m)` are in `QB_A`, being commensurable with `B_3`.
   - All finite direct products and finite extensions of these groups, for example `B_n × H` with `H` hyperbolic.
   - So all of these quasi-isometrically embed in finitely presented simple groups. For the closed genus-two case
     this answers the "(quasi-isometrically?)" refinement of Zaremsky's mapping class group question
     (arXiv:2201.00711v1, TeX l.495–497).

**Not claimed.**
- Closure of `QB_A` under free products. BFFHZ Corollary F gives closure of `B_A`, through `K*K ≤ Aut_K(K*F_n)`.
  Its QI version needs `K*K` undistorted in `Aut_K(K*F_n)`, which is unchecked.
- Whether every finitely presented simple MIF group `K` is undistorted in `Aut_K(K*F_2)`. That would be the QI
  version of BFFHZ Theorem C, and it is unchecked.
- Mapping class groups of genus `>= 3` with punctures and no boundary.

**Lesson for general BH.** The permutational toolkit has a geometric shadow at no extra cost. Type (A) actors
carry fp simple hosts that quasi-retract onto them. Zaremsky's product and finite-index constructions and
retractions all keep undistortion. So every Boone–Higman closure theorem proved through type (A) actors should
be re-audited as a QI closure theorem.
- The audit passes for products and finite extensions.
- It is open for free products and the lamp or graph constructions on main.
- It fails for the economical `Aut(F_n)` inputs of coindex ≥ 2 (`loop-braid-groups-are-distorted-in-aut-free-groups`).

The finite-extension step is also what turns partial results into whole groups: a virtual embedding plus
residual finiteness already settled closed genus two.
