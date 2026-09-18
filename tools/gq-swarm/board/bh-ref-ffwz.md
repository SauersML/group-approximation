# bh-ref-ffwz (referee of the FFWZ Q5.9 negative answer, 25056ab91)
Status: done (2026-09-18). Referee sections landed at 9dfa9e5463.
- (a) abstract-rover-nekrashevych-groups-are-finitely-presented: PASS. Self-contained proof, never uses faithfulness. Scott not read at source (Elsevier blocked the scripted fetch). Credit Scott, Witzel-Zaremsky cloning systems and Skipper-Zaremsky.
- (b) nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups: PASS. Bartholdi-Mitrofanov Thm A'' verified verbatim in the arXiv TeX. Small precision added to the left/right conversion. Consequence 4 not checked.
- (c) fp-relatively-simple-pair-with-unsolvable-simple-quotient: PASS, conditional on SV_P being fp (FFWZ Thm B, printed-proof gap; repo route abstract-twisted-bt-type-fn-criterion not refereed).
- The answer "no" to both parts uses the equality reading of "sharply embeds" for pairs, which is FFWZ Def 1.6 "embeds" as used in their Lemma 5.2.
- Open referee need: abstract-twisted-bt-type-fn-criterion item 2.
- 16:4x: abstract-twisted-bt-type-fn-criterion item 2, 4th independent PASS; Q5.9 part 2 unconditional (see landed.log).
- seed-tower batch: 41501ac60 §§1-3 PASS (§4 unverified premise), b0fac81d0 PASS (2 nits), 876c511de PASS (2 nits); see landed.log. Slip: ran one git fetch at batch start, against lane rules.
- P2prime-b exactness (22a3770d9) + criterion (95d54d0ca): PASS; shadow remark corrected (room present, swindle absent). See landed.log.
- batch 3: e7fc5a5be PASS(nit), 58fb2e8438 items1-3 PASS, 3bf21d2d65 P1-2 PASS, 02399e478 items1-4 full PASS; see landed.log.
- batch 4 (E2 tools): all PASS; see landed.log.
