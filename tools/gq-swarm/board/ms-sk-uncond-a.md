# ms-sk-uncond-a
Direction: the K-theory side of the SK open row (tex l.733-735). This covers the LVFreeAlgK2 / NK2 / Gersten chain and its neighbours, only where nobody has touched it in the last 2 h. As of 20:28Z, no SK commit had landed in the last 3 h.

## Gate map (read from origin/main 1d38dc7fd, 09-18 20:30Z)
- The open row reduces to ONE Prop. `LVWire/Chain.lean` gives it as hD : StableK2Trivial CohnLimit. Two equivalent forms:
  - stable K2(C_2(F2)) = 0;
  - `LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement`.
  Every other link of the chain (descent to L, superperfect, K2(4,L)=bot, EL_5 fp) is proved.
- Weaker entry points that are also sufficient:
  - `LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement` (K2(4,L) finitely normally generated, not bot);
  - `EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`.
- ABC thm:skewyao Step 3: C_{>=0} is filtered by rings F_k with F_0 = F2<x0,x1> (`LVCohnHalf/FreeRep`). The free-algebra K2 (Gersten) is therefore the base input of the route.
- `LVFreeAlgGersten` reduces the Gersten nil part to `skGer_PolyNilStatement` (NK2(F2<x0,x1>) = 0). That residual is a priori STRONGER than the target.

## Landed
(pending probe) Full/LVPolyK2/Basic.lean. It bridges bh-met-94e's K2(N,F_p[X]) = bot into the SK stable-K2 API:
- stable K2(F_p[X]) = 0;
- NK2(F2) = 0, which is the conclusion of skGer_polyNilZModTwo_of_polyNil, now unconditional;
- stable K2 of M_m(F_p)[X] and of (prod M_d(F2))[X];
- stable K2(S[X]) = 0 and untwisted NK2(S) = 0 for every ultramatricial F2-ring S (the phi = id case of LVSkewLaurentK2.NilK2Trivial);
- stable K2(C0[X]) = 0;
- Gersten for ONE generator: stable K2(F_p<x>) = 0 and AugNil(freeAug F2 (Fin 1)).

## Open (not discharged)
- AugNil(freeAug F2 (Fin 2)), i.e. Gersten for two generators, and skGer_PolyNilStatement.
- Twisted NilK2Trivial S (+-1); YaoFactorization.
- Stable K2(C_2(F2)) itself.

## 09-18 ~19:40 (after restart)
- LVPolyK2/Basic.lean was landed by the coordinator sweep (af2506bf1a); its bytes match my overlay.
- SKAttestA/{Intro,General}.lean audit the 100 formalized rows at l.<=480: 241 distinct decls, and all of them resolve inside the 8048-module root closure. Owed binders: only `printedGXAnswersBrownOzawaPestov_of_main` and `printedSimpleKazhdanSoficMain_of_pieces`, and each row also lists its closed endpoint. Before these modules, 89 decls had no #audit line. The coordinator swept both modules onto main (md5 match).
- Branch archive (claude_great-ptolemy): there is NO usable proof. The archived LVFreeAlgK2/Endpoint imports the never-written LVFreeAlgGersten.Endpoint, and the archived LVCohnColimit/Final calls the nonexistent unconditional exists_cohnColimit_embedding.
- Probe of the three modules, empty overlay, against main e6c93a1fe4: queued.

## 09-18 ~21:10 (SLURM-BLOCKED)
- 8bb2199cc2: repaired the stale drafts LVAssembly/Endpoint.lean and LVCohnK2/Final.lean. The branch merge re-added them, and they cited the nonexistent cohn_stableK2Trivial. They are now conditional wrappers on skCohnLimK2_degreeZeroSurjStatement that delegate to SKFix01. Unprobed.
- 89031424b5: Cairn fix node research/fix-sk-cohn-stable-k2-degree-zero-surj.md. It covers the SK open row's single owed Prop: its equivalent forms, its consumers, the proved inputs, and the open sub-inputs (two-generator Gersten; the K2 localization step).
- FIX-GRAPH: my 5 modules are UNPROBED. Probe request 1789778236.67839 (empty overlay: LVPolyK2, SKAttestA x2) is still queued. Once SLURM-BLOCKED is gone, re-probe with those targets plus LVAssembly.Endpoint and LVCohnK2.Final.

## 09-18 ~21:30
- 00afa94386 LVPolyK2/Localization.lean (unprobed). It names skLoc_GerstenTwoStatement (AugNil of freeAug F2 (Fin 2)) and skLoc_LocalizationStatement (Core-B: StableK2BaseSurjective freeToLeavitt), and wires both through stable K2(L) = 0 to the l.733-735 sentence.
- Published at source: ABC arXiv:0903.0056v2 Thm 7.6 (MSI lit-groups/abc-clean.txt l.1064-1075). For the rose, N = (2) and 1 - N^t = -1, so K_n(L_F2(1,2)) = 0 for all n. The Cohn algebra is the Leavitt path algebra of the rose with a sink added (Abrams-Ara-Siles Molina), and the same theorem gives K2(C_2(F2)) = 0.
- Two-generator Gersten does NOT follow from the one-generator proof. That proof is F<x> = F[x] plus the Euclidean/Nagao K2(F_p[X]) = bot. A two-generator analogue would need Cohn's weak algorithm and a new multi-kLOC Steinberg argument.
- Census note: the l.733-735 sentence itself cites Caprace-Remy, so its row could be graded attribution (a census-owner decision; not my call).
