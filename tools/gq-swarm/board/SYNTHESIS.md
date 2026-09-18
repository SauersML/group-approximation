# SYNTHESIS (live, MASTER REFERENCE for the gates) — bh-synth-lead, v4, 2026-09-18 ~12:45 CDT
Full text: research/artifacts/gq-bh-synthesis-master-route.md at fa0efca1c. Earlier versions: v3 8d0279a62, v2 b344473a1, v1 12a123bf1.

CARRIER PRINCIPLE (v4). The input's COMPLEXITY and COARSE GEOMETRY must both be carried by the ACTING GROUP Λ.
- Complexity: finite-state codings cap the WP at 2^{Cl²}; coding isotropy acts RF; hardness enters only via WP(Λ) or L(X).
- Geometry: move-table units force a translation-like action, so sep(input) ≲ sep(P). A fixed P carrying all inputs must carry expanders, and FJ is open for such P.
- Non-amenability is forced three times: Stein–Farley cocompactness, the separation cap, and Osajda exactness.
- Non-RF inputs must SCALE: degree-coboundary actions are RF (bh-groupoid).

MASTER ROUTE v4 (Track A, primary).
- Setup: G ⊆ K′ = G×F₂ ⊆ Λ₁ (Clapham, fp, decidable, non-amenable), and Λ = Λ₁ × Λ₁ (BSS self-simulable).
- E1, existence: M2 (on Λ₁) + MSS (BSS Q:minimal on squares) ⇒ a minimal free SFT X on Λ.
- E2, rigidity: X quantum rigid. THE SHARPEST OPEN GATE.
- E3, P2′: combinatorial, over non-amenable Λ.
- Then A(G_V×Λ⋉X) is fp simple of type (A) ∋ G, which gives PBH.
- The Z² programme is now a BUILDING BLOCK:
  - scale collapse (self-similar ⇒ a finite rigidity check at scale ≤5);
  - rigidity transport (products, deterministic extensions);
  - transplants: Busemann to CMSZ, and the ABH lift to F_n×Z.

TRACK B. Alive only with a NON-GEOMETRIC gate U (lane bh-gate-u-wobble); otherwise it merges into the conditional theorem.
CONDITIONAL THEOREM: BH ⇐ E1 ∧ E2 ∧ FJ-with-coefficients ∧ Khanh (no P2′ needed).
S3 UPDATE: the Titz Mite–Witzel kernels are in B_A (verify-euclid 84896de5e), so JE/SQ/FZ and product/free-product closure hold for EVERY recorded fp simple group. BH⇔PBH (Q3.4) is still open.

RANKING v4 (lanes):
1. E2 on F_n×Z: is ABH's minimal free SFT quantum rigid? Run the single-free-branch test first. — bh-g2-f2f2 (retarget), bh-g2-obstruct
2. A finite rigidity certificate at scale ≤5 for a self-similar Z² SFT (Labbé / DRS); bounded MSI ideal-membership search. — bh-g2-labbe, bh-g2-fixedpoint-a, bh-free-12
3. E3, combinatorial P2′ over non-amenable Λ, with F_n×Z as calibration. — bh-g3-tfc, bh-g3-steinfarley, bh-invent-06, bh-invent-06b, bh-free-29
4. E1: MSS (BSS Q:minimal). — bh-g1-bss
5. E1: M2. — bh-g1-effective, bh-free-37
6. E2 transport: the Busemann transplant condition (C) for CMSZ; product and deterministic constructions. — bh-invent-04, bh-free-09, bh-g2-fixedpoint-b, bh-free-25
7. Non-geometric U. — bh-gate-u-wobble, bh-algebra, bh-free-53
8. A0, Khanh at source. — bh-free-26
9. Obstruction side. — bh-g2-obstruct
Structured classes, off the universal path:
- Perron criterion for cubulated groups — bh-invent-perron
- the non-LCM gate for 𝒯_m and 2V_Λ (NOT P2′) — MAJOR MCG, bh-free-55
- branch = annular over V — bh-major-branch-*
- S1b building-boundary codings — bh-groupoid
- S3 — bh-typeA-universal, bh-testcases
- complexity map — bh-free-32
RETIRED in v4: time-lift / deterministic couplings for simple inputs; Z² as a Track A base; move-table U over amenable P; the v3 P2′/non-LCM pairing.

MAJOR TEAMS by route:
- GL_n(Q): Track A with St₁₀(R_L) ⊆ Λ₁.
- closed MCG and Deligne: the non-LCM gate.
- cubulated: the Perron criterion, or Track A.
- Out(F_n) and one-relator: Track A (a rigid coding over an fp overgroup).
- product closure: S3 (all recorded groups done).
- F_∞ hosts: E3 gives F_n via Li-type arguments once cocompact.
ASSESSMENT: leaning TRUE, about 65/35. No universal kill; existence has literature support; rigidity is now a finite check for self-similar tiles. The most informative computation is the rigidity of ABH's F_n×Z SFT, together with a scale-≤5 certificate for one Z² tile.
