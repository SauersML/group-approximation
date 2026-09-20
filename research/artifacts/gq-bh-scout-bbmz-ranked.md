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
| 1 | Survey Q4.7: one-ended hyperbolic / closed surface groups in V | OPEN (`closed-hyperbolic-surface-groups-embed-in-thompson-v`). Partials by this lane: `topologically-free-fg-subgroups-of-v-are-virtually-free` (refereed PASS, 6a216bf0dc) and `one-ended-hyperbolic-subgroups-of-v-are-locally-fixed` (Lemma L; unreviewed) | 4 | HSZ Thm A (new) + meeting supports (bh-free-41). Such an embedding is locally fixed at every point, has no two disjoint supports, and (torsion-free) has no north–south element. Left: the compression lemma | **bh-scout-bbmz** (taken) |
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

1. **Q4.7, surface groups in V.** Taken by this lane. Lemma L is now proved
   (`one-ended-hyperbolic-subgroups-of-v-are-locally-fixed`); only the compression lemma in its route remains.
2. **Skipper–Zaremsky F_∞ for all contracting V_d(G)**, via the level-set lemma.
3. **BBMZ-hyp Q1.1 beyond surfaces and RACGs.**
4. **BBMZ-hyp Q1.4**, via lift-ideal Theorem A.
5. **Belk–Zaremsky F_n criterion for SV_G**, via T0-style Morse methods.

Kourovka 21.41 is a close sixth. It sits beside bh-kd2p and could go to it.

## Exact statements and notes for the items being staffed (ranked #2, #3, #4)

### #2. Skipper–Zaremsky: V_d(G) of type F_∞ for every contracting G

**Node.** `contracting-rover-nekrashevych-groups-are-f-infinity` (OPEN).

**Statement, verbatim.** Skipper–Zaremsky, arXiv:1709.06524v2, TeX l.1365–1367, as quoted in the node:

> Is V_d(G) of type F_∞ for every finitely generated, contracting self-similar G?

**State on main.**
- The whole question has been reduced to `contracting-groups-have-dying-kernel-covers-of-type-fn` (OPEN): for each
  n, a type-F_n group B with a wreath recursion whose faithful quotient is G, with dying kernel ∪_j K_j.
- The reduction goes through the transfer theorem `wreath-recursion-thompson-groups-inherit-fn` (lane proof,
  bh-free-06; not reviewed).
- **Known cases:**
  - polynomial activity growth (`rover-nekrashevych-polynomial-activity-tower-sigma-full`);
  - bounded automata (Belk–Hyde–Matucci arXiv:2407.03149);
  - IMGs of expanding coverings of compact aspherical spaces;
  - hyperbolic PCF rational maps;
  - Röver's group;
  - n = 2 (Nekrashevych).
- **Obstruction:** torsion-free covers are impossible when a finite-order germ recurs along a ray, e.g. in the
  Grigorchuk group.

**Why the level-set lemma may apply.** `bounded-defect-free-full-contracting-rsgs-are-f-infinity` (refereed at
78857ab1ec; BHM Remark 2.13 attribution) proves that full, bounded, contracting RSGs with defect group finite, or
ℤ with interval defect sets, are F_∞.

**The concrete test.** Take V_d(G) for contracting G:
- it is a full RSG over the full d-ary shift;
- it is contracting, with nucleus N_G;
- for its elements, "bounded" means finitely many singular points;
- H_0 = coker(I − A^T) = ℤ/(d−1) for the full shift, which is finite.

So wherever V_d(G) is bounded, the level-set lemma gives F_∞ directly, bypassing covers. Check first:
- whether bounded-automaton G gives a bounded RSG, which would recover BHM;
- which contracting G give unbounded V_d(G), e.g. via polynomial versus exponential activity, and whether the
  sing(g) dichotomy (5af33a077b) classifies them.

**Caveat.** For the full shift the defect group is finite, so the defect hypothesis is automatic, and the real
condition is boundedness. BHM already prove F_∞ for bounded automata. So the new content would be one of two things:
- showing that some contracting G with *unbounded* activity still gives a bounded RSG, in the singular-point sense,
  which is a different notion from automaton boundedness;
- extending the level-set lemma to the unbounded case.

### #3. BBMZ-hyperbolic Question 1.1: every non-elementary hyperbolic group is a contracting RSG

**Node.** `non-elementary-hyperbolic-groups-are-contracting-rsgs` (OPEN).

**Statement, verbatim.** BBMZ arXiv:2309.06224v3 §1, `ssec:open`:

> Is every non-elementary hyperbolic group isomorphic to a contracting RSG?

**Done on main** (mostly lane proofs, some refereed):
- `G * Z`, and `A * B` for hyperbolic A, B, not both of order 2 (so every freely decomposable group);
- finite-index overgroups, and products with finite groups;
- virtually free groups;
- closed surface groups (0c67e7a290, refereed);
- hyperbolic RACGs with spread nerves (32d05a3242, refereed);
- right-angled reflection groups in H³ and their commensurability classes (a39f0aa949).

**What remains.**
- one-ended groups: general hyperbolic RACGs, closed hyperbolic 3-manifold groups beyond the reflection cases, and
  Kazhdan hyperbolic groups;
- infinitely-ended groups none of whose finite-index subgroups split freely. These are not virtually torsion-free,
  and their existence is open.

**Notes.**
- By finite-index closure, it suffices to do one finite-index subgroup.
- The natural next targets are:
  - all hyperbolic RACGs, extending the spread-nerve coding;
  - then cubulated hyperbolic groups, which are virtually special, via Haglund–Wise, so virtually subgroups of
    RACGs;
  - but being a contracting RSG does not obviously pass to subgroups, since fullness and the RSG condition are
    not hereditary. So the step from RACGs to cubulated groups needs a separate argument, e.g. convex cores, as
    in `convex-cores-inherit-greedy-coding-na`.
- The Kazhdan case is where 07e20250b (uncountable shear frontiers) may bite. Check whether contracting RSG
  structure forces anything about boundary local cut points.
- The sing(g) dichotomy (5af33a077b) is a finite-graph test that may help certify the nucleus finite.

### #4. BBMZ-hyperbolic Question 1.4: full closures of finitely presented RSGs

**Node.** `fp-rsgs-have-fp-full-closures` (OPEN).

**Statement, verbatim.** BBMZ arXiv:2309.06224, TeX l.236:

> If G is a finitely presented RSG, then must the full closure of G also be finitely presented?

**Done on main.**
- Yes for contracting G (`contracting-rsgs-have-fp-full-closures`, via BBMZ Theorem B).
- Trivially yes for full G.
- So any counterexample is non-contracting and non-full.

**First open family** (`v-normalizer-rsgs-contract-iff-finite-outer-order`): Γ_t = ⟨V, t⟩ = V ⋊ ⟨t⟩, for t
normalizing V with infinite order in Out(V). These are finitely presented, non-contracting and non-full. For outer
order ≥ 3 the core is asynchronous (`synchronous-cores-in-out-v-have-order-at-most-two`), so neither BBMZ Theorem B
nor the Scott/SWZ theory applies to [[Γ_t]].

**Why lift-ideal Theorem A may help.** c327ef1ef3 (refereed PASS, both directions) is a finite-presentation
criterion for V_d-type full groups: V_d(G) is finitely presented iff its relators are finitely lift-generated.
- Test whether [[Γ_t]] fits that framework. It is a full group containing V, so ask whether it is V_d(G') for
  some self-similar G' built from t's local actions.
- If so, decide finite lift-generation from t's transducer.
- Also note c2bdf2618d: "the action decides, not the group". The same abstract group can have finitely presented
  and non-finitely-presented V_d, so Q1.4 may fail through a persistent-type action.
