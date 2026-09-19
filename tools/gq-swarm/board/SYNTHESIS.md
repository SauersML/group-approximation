# SYNTHESIS (live, MASTER REFERENCE for the gates) — bh-synth-lead, v7, 2026-09-18 ~17:10 CDT
Full text: research/artifacts/gq-bh-synthesis-master-route.md at a85dd1c95. Earlier: v6 b5ad39956, v5 16bd19b7f, v4 fa0efca1c, v3 8d0279a62, v2 b344473a1, v1 12a123bf1.

THESIS v7: E1 AND E2 ARE EACH CLOSED (modulo review), BUT FOR DIFFERENT SFTs. THE CARRIER IS LEFT, AND IT MEETS GROUP EXACTNESS.
- E1 (74597e3ce; bh-ref-e1-a/b): a minimal free SFT over Λ = ((Λ₁×Z)∗Z)×Z².
  Clapham gives decidability, the storage Z gives (D), the gluing Z gives minimality, the Z² keyed slots give finite type.
- E2 over Z² (49939b957; bh-ref-engines): the crossing-wire fixed-point shift, free, minimal and rigid. The mechanism is co-location.
- (C) passes review for folds and transplants (cb53a036f; cylinder transport db6f1ea68). Kazhdan Ã₂ / F_m×F_n / BMW free rigid SFTs are conditional (7d228882f).
WHAT IS LEFT FOR FULL BH:  BH ⇐ CARRIER ∧ ( (A₂) for its SFT ∨ (FJ(Λ) ∧ Khanh) ).
- CARRIER (★′): ONE SFT over an fp overgroup of the input that is minimal, topologically free AND rigid.
  E1's SFT carries the input but is not known rigid. E2's SFTs are rigid but carry no input. This is the only input-dependent statement.
- (A₂) = E3′ (89fbf22bb): finiteness is horizontal, i.e. F_n ⟺ essential (n−1)-connectivity of the domain filtration.
  It contains P2′b = PRESENTATION exactness (K = 1), which is input-free and uniform:
  - one-transposition criterion (95d54d0ca);
  - self-swap coherence (CL) (02399e478);
  - LTP + EX(Z) (72e3b699d);
  - all fg groups reduce to FPG + EX(Z) monodromy on 2ⁿ-letter full shifts (96d92cb72);
  - V_(2,2) is exact (f040a4fa6).
- Ring route: FJ + Khanh, and no (A₂).
THE WALL = GROUP EXACTNESS (property A; not presentation exactness):
- BH forces an fp simple NON-EXACT group: Osajda's decidable non-exact group plus the exactness separator (exactness-separates-...).
- (RA) (quantum-rigid-minimal-topfree-subshift-actions-are-amenable, OPEN): rigid minimal topologically free subshift actions are amenable.
  It is proved over F_n; over Λ₀×F_n measures live on TIGHT points (f676c07d2). Every rigidity mechanism and every transport on main is amenable.
- If (RA) holds: there is no carrier over any overgroup of Osajda's group, and (by necessity) no fp V-full group of a minimal topfree subshift over a non-exact group.
  So every track, seeds included, is confined to exact inputs. Track B's linear gate U hits the same wall (Kirchberg shadow, 926454737).
SINGLE DECISIVE STATEMENT: ¬(RA) AT OSAJDA'S INPUT. Some fp overgroup of a decidable non-exact group carries a minimal topologically free rigid SFT.
- A counterexample must be TIGHT, i.e. slab-determined with no free branch (synthesis remark).
- Design target: a slab-determined crossing-wire keyed-slot lift of the E1 SFT, with (C) by cylinder transport and no cross-layer separable modifications.

GATES v7 (rank · gate · lanes):
1. ¬(RA) at Osajda's input (tight carrier), or prove (RA) beyond F_n (Λ₀×F_n, then A∗Z) — bh-star-a, bh-star-b, new lane
2. Carrier for exact inputs: rigidify the E1 SFT (crossing-wire keyed slots; (C) for the A-data layer; single free branch along A∗Z) — bh-g1-bss, bh-g1-simulation, bh-g2-fixedpoint-a, bh-free-09
3. CAP, the complexity face (seeds):
   - seeded ⇒ solvable WP (a9187d6d4); κ sandwich (b970e40ae); locally finite part of 𝒞 is elementary (fed877149); distortion certifies nothing (17f8da472);
   - relative seeds glue (5deee0184); the Higman coupling is one HNN along graph(F→G) (41501ac60, 0d6bf2845).
   TEST: a rigid relative seed for (K_M, R_0) — bh-invent-03/14/15, bh-emitter-a
4. (A₂) for the carrier's SFT; EX(Z) monodromy + (CL) + FPG — bh-invent-17, bh-p2b-exact, bh-one-relator, bh-invent-16
5. Reviews: E1, crossing-wire rigidity, the 7d228882f layout lemma, Q1.15 — referee lanes
6. Imports for the ring route: FJ for ((Λ₁×Z)∗Z)×Z²; Khanh
7. Q3.4 residue after Q5.9 = NO: BFFHZ Q3.2 for non-MIF (circle-type) fp simple groups, first test T — bh-ffwz-q59
STRUCTURED:
- Q1.15 CLAIMED YES (877d63985, flagged cube category + Cuntz; referees running).
- MCG: sync in every rank (e0337551b), Ore = tree domination (141898aff); fp of the rational projective full group and the tracking lemma are OPEN.
- H4/BG: G₁ and all finite BS chains are in B_A (80ce687aa, 23e5c5c7d); only global symmetry is left.
- Hyperbolic F_∞: a finite no-cycle test (C) plus colour-tameness (04ac193c1).
- GL_n(Q): the (SL) fp RF semilocal bottleneck (9d121fa9c).
RETIRED v7:
- Track C / stabilizer engines (a23f54860 PASS);
- kernel removal as a PBH constructor (Q5.9 NO, 18523f6b4);
- distortion as a CAP test; locally finite seed towers;
- fibre-product rigidity and the "common determinism cone" rule;
- P_eff (49984b668);
- passive labelled enlargements;
- homology refuting Q1.2.
v6 CORRECTIONS: CAP is demoted to the complexity face ((RA) covers all tracks); FSG(Z,2) is now EX(Z).
NAMED SINCE v6: MO 339541 fully answered (Reid's group not fp, PASS); FFWZ Q5.9 NO (PASS); Kourovka 17.61 (PASS); BFFHZ Q3.1 (PASS); T_{2,3}, T_τ are F_∞.
ASSESSMENT: ~60/40 TRUE (was 65/35). E1+E2 is progress, but every rigidity mechanism is amenable while BH needs a non-exact fp simple group.
NEXT PROOF: (RA) at Osajda's input. Build a tight carrier, or extend the end map to Λ₀×(A∗Z).
