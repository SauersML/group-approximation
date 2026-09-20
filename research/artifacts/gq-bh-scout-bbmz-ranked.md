# Open Boone–Higman questions ranked by tractability with the tools on main (09-19)

Lane `bh-scout-bbmz`, 2026-09-19, reading main at `29f44638b`.

**What this file adds.** It updates two earlier files:
- `bh-survey-open-cases-status-2026-09-12.md`, the survey read page by page with verbatim wording;
- `gq-bh-bh-bbmz-problems-status.md` (09-18), the BBMZ-hyperbolic, Zaremsky, BFFHZ, FFKLZ and FWZ questions.

It also draws on the open-questions list in `$GQ/board/UNOWNED.md`. The wording is not repeated here.

**New columns.**
- **Owner:** a *live* lane on 09-19. The 09-18 owners (`bh-free-*`, `bh-mcg`, …) are stopped.
- **Tract.:** tractability from 1 (no tool on main bears on it) to 5 (a tool on main nearly settles it). It is
  measured against the tools landed on 09-19:
  - T0 is F_∞ (db0daa1547);
  - lift-ideal Theorem A for V_d(G) (c327ef1ef3);
  - the level-set lemma (78857ab1ec);
  - the sing(g) dichotomy (5af33a077b);
  - FH chart coordinates (4c81e934b2);
  - the CT(ℤ) undecidability machinery (a95cb1edf, 71b76e027).
- **Solved since?** An arXiv search on 09-19. No new solution of any listed item was found. The one new
  relevant paper is Hyde–Skipper–Zaremsky arXiv:2605.20564v2 (May 2026), Theorem A: orbit Schreier graphs of
  finitely generated subgroups of V are quasi-trees. It bears on Q4.7; see row 1.

## Ranking

| # | Question | Status on main | Tract. | Tool, and why | Live owner |
|---|---|---|---|---|---|
| 1 | Survey Q4.7: one-ended hyperbolic / closed surface groups in V | OPEN (`closed-hyperbolic-surface-groups-embed-in-thompson-v`); new partial `topologically-free-fg-subgroups-of-v-are-virtually-free` (this lane) | 4 | HSZ Thm A (new) + meeting supports (bh-free-41). Such an embedding has no free orbit, is never topologically free, and has K countable with cyclic stabilizers. Left: Lemma L and the compression step | **bh-scout-bbmz** (taken) |
| 2 | Skipper–Zaremsky 1709.06524: V_d(G) is F_∞ for every f.g. contracting G | reduced to `contracting-groups-have-dying-kernel-covers-of-type-fn` (39552185a) | 4 | Level-set lemma (bounded full contracting RSGs with ℤ or finite defect are F_∞) and lift-ideal Thm A for the F_2 step. Check whether V_d(G) is a bounded RSG with interval defect sets | none |
| 3 | BBMZ-hyp Q1.1: every hyperbolic group in a contracting RSG | done for closed surfaces (0c67e7a290), spread-nerve RACGs (32d05a3242), right-angled reflection groups in H³ (a39f0aa949) | 3 | sing(g) dichotomy (finite-graph test) and the RACG coding machinery. Next: all hyperbolic RACGs, then cubulated hyperbolic groups via special cube complexes | none |
| 4 | BBMZ-hyp Q1.4: fp RSG ⇒ fp full closure? | OPEN (bh-higman-classic 09-18, stopped) | 3 | Lift-ideal Thm A is a finite-presentation criterion for exactly this kind of full group over V_d | none |
| 5 | Belk–Zaremsky 2001.04579 conjecture: type F_n criterion for SV_G, n ≥ 3 | node `twisted-brin-thompson-type-fn-criterion` (bh-typeA-universal, stopped) | 3 | Stein–Farley descending-link and V-height methods, as in the T0 proof (Region B repair, bb16c96e08) | none |
| 6 | Kourovka 21.41 (Dantas–Sidki): torsion-free fp metabelian self-similar group containing Z ≀ Z | OPEN; affine witnesses excluded | 3 | The KD2_p line (2843d4965c), with C_p ≀ Z² on the p²-adic tree (6c39124b28) | adjacent to bh-kd2p |
| 7 | BBMZ-hyp Q1.2: full contracting RSGs are F_∞ | partial (78857ab1ec); Kazhdan obstruction (07e20250b) | 3 | level-set lemma, sing(g) | bh-q12-kazhdan, bh-q12-alt-host |
| 8 | Survey 5.3(12) fp residually finite; route via fp self-similar overgroups | OPEN | 2 | KD2_p, finite-recursion depth (e6f7e2b3d7) | bh-kd2p, bh-birget |
| 9 | Survey 5.3(5), GL_n(Q) into fp simple | OPEN | 2 | — | bh-glnq-fresh |
| 10 | HKUW 2508.21264: graph Houghton groups | reduced to `eventually-rigid-g-automorphism-groups-are-finitely-presented` | 2 | needs a bounded-support presentation of Aut_G(G∗F_n); no 09-19 tool | none |
| 11 | Survey Q5.6: every fp group in an F_∞ group | OPEN claim nodes | 2 | none direct | none |
| 12 | Zaremsky 2405.18354 Q5.13 (i)/(ii) | equivalent forms on main | 2 | — | none |
| 13 | BBMZ-hyp Q1.3, Q1.5, Q1.6 | OPEN (Q1.6 reduces to Q5.13(ii)) | 2 | — | none |
| 14 | BFFHZ Q3.2 (for T), Q3.4, Q3.6 (Kac–Moody high transitivity) | Q3.3 answered no on main; the rest OPEN | 2 | — | none |
| 15 | FFKLZ 2506.02319 Q2.4; FWZ Q5.7/Q5.9 | OPEN | 2 | — | none |
| 16 | Survey 5.3(9) one-relator; 5.3(10) CAT(0); 5.3(13) Artin D̃_n, Ẽ_{6,7,8}, F̃_4 | OPEN, with much 09-18 work on main | 2 | none new | none |
| 17 | Survey 5.3(2) closed MCG genus ≥ 3; 5.3(3) Out(F_n), n ≥ 3; Remark 5.5 PIP | OPEN | 1 | — | none |
| 18 | Survey 5.3(6) free Burnside; 5.3(11) automatic | OPEN | 1 | — | none |
| 19 | Kourovka problems in the CT(ℤ) and Thompson families | see `ce7ab8f74`, `UNOWNED.md` | — | CT(ℤ) machinery | bh-kourovka-scout, bh-2174-rank2, bh-2044-tc, bh-1946 |

## Top five unowned, for the coordinator

1. **Q4.7, surface groups in V.** Taken by this lane. The next steps are Lemma L and the compression step
   (route of `topologically-free-fg-subgroups-of-v-are-virtually-free`).
2. **Skipper–Zaremsky F_∞ for all contracting V_d(G)**, via the level-set lemma.
3. **BBMZ-hyp Q1.1 beyond surfaces and RACGs.**
4. **BBMZ-hyp Q1.4**, via lift-ideal Theorem A.
5. **Belk–Zaremsky F_n criterion for SV_G**, via T0-style Morse methods.

Kourovka 21.41 is a close sixth. It sits beside bh-kd2p and could go to it.
