# gq-referee-b — referee, citation/hypothesis-match lens

**Approach.** Waiting for review requests (SendMessage `gq-referee-b` with the node paths). For each request:
read every cited theorem at its source (arXiv abs/HTML, the stated version and theorem number), check each
hypothesis against the use, check countable vs finitely generated inputs, land
research/artifacts/gq-referee-b-<id>.md with a verdict of PASS or FAIL and the exact mismatch, and SendMessage the
verdict to the author and team-lead.

**Standing checks I will apply** (read before submitting):
- Zaremsky type (A) (arXiv:2405.18354; survey Thm 4.15): G finitely presented, faithful, point stabilizers
  f.g., finitely many orbits of two-element subsets. The simplicity of SV_G is a separate claim; check it at
  Belk–Zaremsky (G&T 26 (2022)), not only in the Cairn paraphrase `twisted-brin-thompson-finite-presentation-criterion`.
- The repo's host equivalences (`permutational-boone-higman-iff-finitary-alternating-hosts`,
  `type-a-action-gives-boone-higman-for-subgroups`) are stated for f.g. H or "every subgroup". Any use for the
  countable, non-f.g. GL_n(Q) must say which form is used.
- BHM finite germ extensions (arXiv:2407.03149 Thm 2.1): its finite-presentation hypotheses on the
  stabilizer subgroups S(M,M') must be checked verbatim, not by analogy with VA.
- Zaremsky 2405.09722 Thm 1.2 covers f.g. subgroups of GL_n(Q) only. Citing it for GL_n(Q) is a FAIL.
- O1: any intermediate overgroup of (Q,+) that is residually finite (linear over a f.g. ring, self-similar, a
  tree group) is a FAIL.

**Reviews.**
- sl-n-q-is-colimit-of-lattice-stabilizers (gq-k2-q): PASS conditional on A1 (I3 is for simplicial complexes; use the staircase triangulation of X_S) and A2 (I2 via Kramer arXiv:1009.3089 section 6.4(a)). Report c1ce2c85d.
- lifts-add-no-unipotent-divisibility (gq-pp-lift): PASS. germ-extensions-omit-standard-gl-n-q (gq-pp-higher): PASS + wording. piecewise-commutative-linear-hosts-miss-linear-gl-n-q (gq-solenoid): PASS + wording. b8319c330.
- leavitt-pairs-embed-sl-n-q-in-steinberg-groups + Problem 2.7 route (gq-steinberg-q): lemma PASS; route PASS if A1 (cite Krstic-McCool via Khanh 2609.08428v1 Thm 6.1, EJZ Thm 1.1) + A2 (split ring part 1). 2547e90a5.
- leavitt-resolvent-ring-is-fp-simple-of-char-zero (gq-ring-fp-simple): PASS; criterion unrefereed, used parts checked; novelty bounded. dfd8468b9.
- permutational-host-forms-agree-for-countable-inputs (gq-typeA-design): PASS, BFFHZ Rem 3.5 + Thm C verified; VA in B_A. fd335d944.
- one-steinberg-group-contains-every-gl-n-q (gq-deep-free-1): claim PASS; route needed R_L. 0696f7a28.
- leavitt-scalar-commutators + resolvent units not fp (gq-ring-leavitt): PASS. c81257d90.
- Ihara citation + SL_2(Q) via Hecke/BLIW (gq-infinite-primes): PASS; H1-H4 node not reviewed. 1f1c1af7a.
- St_{3N+1} sharpening + quotient relators (gq-steinberg-q): PASS. f60c835bf.
- nV Kazhdan routes (gq-nv-obstruct): PASS, conditional. 0c5ef12bf.
- pp-circle citations (gq-pp-psl2q): PASS. 595ca31dd.
- Laurent symbols, symbols, tracial part 4 (gq-deep-adelic-1): PASS, trust surfaces T1, T2. 07f514d71.
- gq-referee-c direct St_n fp (n>=5); q-algebra-elementary-quotients (gq-en-ring); one-manifold hosts + Witte via Parwani Thm 1.2 (gq-deep-pp-2); integral-leavitt-unit-group-contains-q (gq-deep-ring-1): all PASS. 95b06dff9.
- Four ring envelope theorems + two OPEN nodes (gq-ring-fp-simple): PASS. d7414d7a4.
- SMART level-0 odometer factor + route (gq-nv-obstruct): PASS; minimality trust surface T1. 628a5c79d.
- Z_(l) in fp Kazhdan St_N(R_l), Steinberg-RF => ring-RF, G_l wording (gq-infinite-primes): PASS. 982f98fc3.
- SMART height-3 renormalization + BS(1,3) in 3V route + criterion (gq-nv-obstruct, gq-affq): PASS; relay needs referee-a + priority. b6d33ae8e.
- SL_3 congruence transfer + Toeplitz citations (gq-deep-adelic-1): PASS; Loday T3 stays. e967829ec.
- fg semiprime PI Q-algebras (gq-ring-fp-simple): PASS + W1 multilinearize, W2 Bergman gap. fbf1d1170.
- Local annihilation + PE_N(R_T) simple + host route (gq-en-ring): PASS; R_T ring parts 1-3 have ONE referee pass (a), not two. 61ed26df4.
- R_T ring parts 1-5 + harmonic elimination, PROOF review (second referee): PASS; parts 1-3 now double-refereed. 4597db9ae.
- Bounded-harmonic rings not fp (refutes E_N(R_T) fp; R_T route dead) + Leavitt tuples make (Q^x)^(d-1) elementary (gq-steinberg-q): PASS. aa01c8044.
- Resolvent vacuum no-K0-state + OPEN divisible-unit target (gq-ring-fp-simple): PASS; W3 example convention (A_ij = edges i->j). 9a2dd39e7.
- Register-comparison presentations not simple (gq-ring-fp-simple): PASS; W1 P_f over every field, W2 relations in B, W3 C1 only via C4. 86f70e504.
- register-completion-pimsner-from-supercoherence (gq-ring-fp-simple): FAIL as written (G1 Prop 7.1 outside hyps, G2 Morita claim false, G3 regrading), repairable; eventually-rational B+ supercoherent by citation (arXiv:2509.05109 Prop 4.36). 27950613e.
- PGL_2(Q) in rational group + Aff(Q) in Aut(V) facts (gq-deep-free-3): PASS. ff17d3b47.
- register-completion re-review (gq-ring-fp-simple): repairs PASS; A1 scope needs point indicators (R_L not covered). 852a0771f.
- R_l residually finite + rank-five routes + K_2 heuristic (gq-infinite-primes): PASS; 4 imports to mark. ef36a82a9.
- A_1 (prime-shift affine) not fp (gq-ring-fp-simple): PASS; type (A) route dead as stated; K_n wording fix. 011cfe05d.
- resolvent corner symbols survive (gq-k2-q): PASS; K_rf not fin. normally generated: correct GIVEN Dennis-Stein + van der Kallen, NOT confirmed at source. c73393b35.
- KMS no-Z_(l) (gq-infinite-primes): PASS, 7 wording fixes (false quote, S_3(X), ZN_3 slip in KMS Thm 4.19). 792755b61.
- KMS configuration letters + KMS reading section 4 + Rauzy Thm 1 (read v2 PDF): PASS; commutator convention unprinted, G7 unused, Wehrfritz unread. 97d621b3b.
- DS (LNM 342 pp. 254-255) + vdK (LNM 551 Thm 1 p. 77) read at source: CONFIRMED; K_rf flip stands. 7a9be50ac.
- Z_(l) tree lemma + free-group mapping tori (gq-k2-q): PASS; edge-stabilizer overclaim, Z[1/P] chain, uncited non-linearity (applied 6f285b1d1). 1aaec95af.
- Euler base annihilator over the lamplighter (gq-infinite-primes): PASS; BR remark convention slip. 86b226622.
- Ascending HNN of free groups contain no Z[1/P] (gq-k2-q): PASS; Stallings read at source (Kapovich-Myasnikov math/0202285v1). 9271dcccb.
- Euler base in St_N(T_l) (gq-infinite-primes): FAIL in item 3 (diag(g,g^-1) not a hom), repair psi embeds G_l in E_3; T1 via Xi 1107.5380 L4.1, T3 centrality via Voronetsky; Stafford needs right noetherian, vdK Thm 1 commutative. 76fc7667e.
- Prime-shift K_n reduction (gq-ring-fp-simple): PASS; Bieri-Strebel via Cooper-Tillmann 1506.01793 sec 3.1; 4 scope fixes. 54a1f7ea7.
- Euler ring rational symbols (gq-k2-q): PASS; refutes fg central unstable K_2; withdrew my SK_1(A)=0 remark. ffc9b7392.
- p-adic dilation normalizers (gq-ring-fp-simple): PASS; six exponentials pinned to Serre SDPP 1965/66 exp. 15 Thm 1, read at source; chain case open (a=b=2). fa0354c53.
- Finite-state Mobius pieces + Iwahori Attempt 5 + Euler finite-state Attempt 2: PASS; lemma for Reading bullet 3 supplied; "some generator" wording. e75dc3fc0.
- Torus amalgams of adelic groups (gq-infinite-primes): PASS; Cornulier Thm 1.1 + Ex 3.5 read in PDF, match; Baumslag title corrected. 581236183.
- Algebraic closure kills rational symbols (gq-infinite-primes): PASS; T, S, IS, bimultiplicativity all pinned in DS survey + vdK at source. fad9054a8.
- K_infinity simple localization (gq-ring-fp-simple): PASS; Baumslag PAMS 35 (1972) + Oinert Thm 6.13 pinned; group-ring precursor noted. 7b8ecc64e.
- Euler ring symbols in small finite quotients (gq-k2-q): PASS; DS inputs at source, Stein hypothesis wording. 9897cd0b4.
- One-sided inverses cannot repair the Steinberg residual (gq-k2-q): PASS. aed11c799.
- Coordinator queue (5 second reviews): all PASS. Euler triangular retract 9fd6ca4df (W1 R_l symbols, W2 title); unimodular line pairs 52fc925a5; graded degree-one units e39e24bdb; T_p Attempt 4 30ac03e75 (Quillen applies, D left regular noetherian; ABC for Z[u]); renormalization return times fba51b1a0 (W1 calibration OPEN).
- T_p Attempts 5-9 (central deformation, gq-k2-q): PASS; Quillen/NK pinned to Weibel K-book V.6.2-6.3; DS detector needs F perfect; reverse inclusion I_rf(T_p) supplied. d746cbee4.
- Isometric shift frames over UHF bases (gq-infinite-primes): PASS; title W1. a141e77ba.
- Frame-generated simple rings have no vacuum + gate Attempts 9-10 (gq-infinite-primes): PASS; W1-W3 scope. 90878481c.
- Unit symmetries of a core + gate Attempt 11 (gq-infinite-primes): PASS; Jordan Thm O needs sigma-fixed unit (Baeck-Richter Thm 3); W1 generation not presentation, W2 non-sigma-simple cores open. af0cad75d.
- Torsion K_1 mod central scalars (gq-k2-q): PASS; (C) pinned Weibel K-book III Def 5.10; (G) DS p. 257 verified. 6d3af2e91.
- Isometric frames over rank-one bases + gate Attempt 12 (gq-infinite-primes): PASS; BC pinned Weibel I Ex 1.5, filtered K_0 Weibel V.6.4; W2 item 3 only ranks divisible by j. 5d2294421.
- Degree-one corner unitaries + gate Attempt 13 (gq-infinite-primes): PASS; Morita pinned Weibel III 5.6.1-5.6.2; no-Pimsner claim correct; W1 title matricial. c3e534995.
- Mixed-degree units (gq-infinite-primes): PASS; ABC corner NK=0 is in proof of Prop 7.5, transfers to ultramatricial core; index formula unsourced. f9605d67e.
- Frame designs bracket (gq-infinite-primes): FAIL repairable; item 7 reduction, What-remains misses non-spanning positive v and rank-one infinite sr. 1805e6063.
- Odometer 2V fp simple contains BS(1,2) (gq-affq): PASS; Li ex:ZS(III)+(F), Matui simple2 (Hausdorff explicit l.347), Exel-Pardo odometer, all vs local TeX. 72a3c51ff.
- Out(V) root problem for the 2-shift (gq-infinite-primes): PASS; BBCO lines match, Salo v2 PDF verified, Boyle 2008 preprint reached (root problem not located); W1 commented-out theorem, W2 alphabet independence. 97242cc3b.
- R_L K-theory shifted rational (gq-infinite-primes): PASS; register Pimsner hypotheses checked over B+; Quillen localization, pushforwards, homotopy invariance, product=symbol, excision pinned in Weibel III-V; colimit route replaces excision. 298991936.
- Lift-presented automaton groups BH (bh-self-similar): PASS with C1 (consequence 3 covered by Scott FP1 + Zaremsky) and C2 (SWZ Ex 7.2: hypothesis is about the action; V_2(Grig) F_infty); Zaremsky (R), Nekrashevych 4.7/4.8, VV, SVV read at source. f957e7bd7.
- Leavitt refinement unstable K2 levels (gq-infinite-primes): PASS; Voronetsky 2004.08551v2 Prop 1 read at source (S={1}, n>=4 bijection, any unital ring with Morita-equivalent family); Khanh padded centrality; Weibel III 5.5. dcf202f7c.
- Aut/Out(F_n) abelianized extension virtually splits (bh-outfn): PASS; conventions match; source for cocycle Kawazumi math/0505497 (2.5),(2.11); W1 Attempt-4 wording. e2559641e.
- BG in isometric brick hosts (bh-one-relator): PASS; 2V_tau, 2V_{G_N}, V_2(G) checked as isometric-section brick groups; entropy bound unpinned, spanning-set proof supplied. a8dffeea3.
- BH separators omit nested decidable hosts (bh-refute): PASS; Belk-Bleak, Brin, Bleak-Salazar, Mihailova, Zaremsky quote, Birget pinned; W1 hardest-known unsourced, W2 T monotone, W3 Miller unpinned. cabab5c05.
- Leavitt tuples scalar clauses (gq-infinite-primes): PASS with C1 (d-merge = (d-1)-fold iterate of Voronetsky Prop 1) and C2 (lambda^N not injective for even N). bd0d11d05.
- BLIW 11.1 type-A, arithmetic NSP faithful members, CAT(0) tree factor (bh-cat0): PASS; BLIW PDF read (Lemma 10.1 H_e=G_e, Lemma 8.3, Remark 12.7); Rapinchuk 2.3, Foertsch-Lytchak 1.1 pinned; W1-W4. 613ac7fec.
- Queue: bh-cat0 2 (arithmetic Lie lattices BS members, H^2 x tree, a732dc8b6); bh-typeA-universal (hyperbolic-groups-lie-in-the-permutational-class, BBMZ labels, fa1747017, 6932547c3; bbmz-oligomorphic Q1.5/Q1.6 lower priority); bh-refute 2 (decidable-group-with-coarsely-embedded-expanders-exists, coarse-embeddability-separates-boone-higman, Osajda, Gruber-Sisto, LS V.4.3, 8093ecc84); bh-self-similar 2 (loop-retraction-forces-fp-eventual-section-groups, linear-activity-automata non-fp, persistent-subexponential finite, 70ac9f576); bh-kazhdan-inputs (kazhdan-almost-v-central-v-elements-proof BBGGHMS 1107.0672; normal-germ-extensions-of-v finite Kazhdan, BHM Cor 2.10); bh-map (houghton-like shift-similar, Mallery-Zaremsky 2202.00822, Zaremsky 2405.18354 Prop 5.3, 9b43b26d1).

**Established.** none (referee lane).
**Needs.** none.
**Dead.** none.
