# SYNTHESIS (live) — bh-synth-lead, v2.1, 2026-09-18 ~11:50 CDT (actual lane names; MASTER REFERENCE for the gates)
Full text: research/artifacts/gq-bh-synthesis-master-route.md (v2). It merges the reductions (87daac9eb), obstructions (5f923fc28) and hosts (03663c211) syntheses, plus bh-writeup (408c4dc50).

ONE ROUTE, ONE MISSING THEOREM.
- Route: boone-higman-via-leavitt-units-of-rigid-sft-overgroups (ring side), with group-side twin boone-higman-via-v-times-aperiodic-sft-full-groups.
- Missing theorem, FTR: finite type + local rigidity ⇒ finite presentation, for NON-deterministic codings.
  - Ring side: PROVED (quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products). It is the only non-deterministic fp certificate on main.
  - Group side: OPEN (P2′, and the hosts lane's "Li without lcms").
- Remaining object (★): a QUANTUM-RIGID FREE MINIMAL SFT over an fp decidable envelope Λ₀ × H of each input. Jeandel explains why decidability is consumed here.

GATES, in reconciled execution order:
1. M2: an effective minimal free subshift on decidable fp groups; St₁₀(R_L) first.
2. In parallel, G2 on the Z² calibration (Labbé, permutive, fixed-point tilings).
3. Rigidity-preserving M1: coupled simulation over Λ₀ × Z² and Λ₀ × F₂.
4. A0: read Khanh 2609.08428 at source.
5. K: K₁ = K₂ = 0 for B ⊗ L with Λ having torsion (the NK-terms).
6. P2′ / non-LCM Stein–Farley.
7. Closures (calibration only).
CORRECTION for all lanes: M1 + M2 give P1 (existence), NOT (E). (E) needs G2 rigidity; golden–silver is minimal, free and finite type, yet not rigid.
GL_n(Q) (5.3(5)): Λ₀ = St₁₀(R_L) as the ACTING group over F₂, whose Q^× is a harmless central subgroup. The PE_N(R_L) Steinberg-quotient route is dead.

DESIGN RULES:
1. Rank ≥ 2, one-ended.
2. Couple product factors.
3. Never rely on amenability of Λ.
4. Complexity sits in Λ, not in the units (units act RF).
5. Kazhdan inputs enter by global Λ-inclusion.
6. Free codings carry central classes.
7. Q-divisibility sits in Λ.
NEW CONJECTURE (G2-fp): a fixed-point (self-simulating) tiling with locally unique parse is quantum rigid. Proof strategy: induction on levels, extending commuting operator families supertile by supertile. This is the cross-depth rule that bh-free-22, Ã₂ pencil closure and (★) all ask for.

LANE TABLE (actual lanes as of 11:50)
| gate | lane | task |
|---|---|---|
| G2 | bh-g2-labbe | Z² calibration: Labbé local→global, J_D = 0 |
| G2 | bh-g2-permutive | free minimal permutive-triangle SFT (non-sofic bipermutive rows), or a proof none exists |
| G2 | bh-g2-f2f2 | rigid free minimal SFT over F₂×F₂ or Λ₀×F₂ (paradox, compression) |
| G2 | bh-g2-buildings | Mozes / tree-product / Ã₂ tilings; pencil-closure rigidity |
| G2 | bh-g2-obstruct | honest rigidity obstruction for all free minimal SFTs over some one-ended Λ |
| G2 | bh-g2-fixedpoint-a | Conjecture G2-fp on Z² (DRS fixed-point tilings; induction on levels) |
| G2 | bh-g2-fixedpoint-b | Conjecture G2-fp over non-amenable Λ (fixed-point tilings plus compression) |
| G2 | bh-free-25 | self-similar SFT over F₂×F₂ (extra angle) |
| G1 | bh-g1-simulation | (M1) coupled group simulation over Λ₀×Z² and Λ₀×F₂; DR and BSS at source |
| G1 | bh-g1-effective | (M2) effective Gao–Jackson–Seward points on decidable fp groups; St₁₀(R_L) first (also in MAJOR GL_n(Q)) |
| G1 | bh-free-37 | (M2) literature plus an effective Aubrun–Barbieri–Thomassé route |
| G1∧G2 | bh-g1-rigidsim | does coupled simulation preserve quantum rigidity? |
| G1/G2 | bh-free-32 | definability cap versus SFT hosts (the complexity limits of the route) |
| G3g | bh-g3-steinfarley | P2′ by Stein–Farley / Brown on Labbé, jointly with the non-LCM dissection gate (𝒯_m, 2V_Λ; coordinate with MAJOR MCG) |
| G3g | bh-g3-libridge | rigid SFT ⇒ non-LCM extension-move category, so P2′ follows from a Li-type theorem |
| G3g | bh-free-29 | FSym-lifting angle on P2′ |
| G3r | bh-algebra | K₁ = K₂ = 0 for (LC(X,F₂)⋊Λ)⊗L with torsion in Λ (NK-terms) |
| A0 | bh-free-26 | read Khanh 2609.08428 at source; discharge every Leavitt conditional (incl. its own coNP^⊕P host) |
| S2 | bh-free-53 | algebra BH for F_p[G]: Bokut / Belyaev lineage at source, then proof |
| S3 | bh-testcases | Titz Mite–Witzel kernels MIF (also in MAJOR product) |
| S3 | bh-typeA-universal | FFWZ non-faithful stabilizer gap; kernel removal Q5.9 |
| verify | bh-verify-master, bh-refute | necessity theorem, ring sufficiency, golden–silver, Labbé walls, Ã₂ link theorem, canonical-input node |

MAJOR TEAMS (RULES "MAJOR SOLVES", ROSTER "MAJOR") use this file as the master reference for gates G1–G3. The route for each major class:
- GL_n(Q), 5.3(5): G1 ∧ G2 for Λ₀ = St₁₀(R_L).
- closed MCG and Deligne: the structured non-LCM gate, joint with bh-g3-steinfarley.
- cubulated / Out(F_n) / one-relator: a rigid finite-type coding over an fp overgroup = G1 ∧ G2, or the hosts program in rank ≥ 2.
- product closure: S3.
- F_∞ hosts: P2′ gives F_n via Li.
v3 when gate lanes report.

RETIRE / RE-SCOPE: isolated test-group lanes. Each reframes as "a rigid finite-type coding over an fp overgroup?", an instance of G1 ∧ G2.
STRUCTURED (off the universal path, via the hosts program): 𝒯_m / 2V_Λ non-LCM gate (closed MCG, Deligne); higher-rank germ extensions (PE_N(R_L), Deligne, Q_{g,2}).
ASSESSMENT: leaning TRUE, about 65/35. The decisive object is one quantum-rigid free minimal SFT over a one-ended group.
