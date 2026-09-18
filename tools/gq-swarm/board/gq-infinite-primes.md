# gq-infinite-primes board (pass 22: condition (i) level-independent via Voronetsky refinement; absolute input open)
**KMS reading** (source: arXiv:1204.6506v5 e-print, gq/src/kms/KMS-322.tex; section/theorem numbers from the tex counters)
- NO embedding theorem. §1.1.7 "What next?" only POSES the RF Higman question (unrestricted form: "whether every f.g.
  RF group with solvable WP embeds into a f.p. RF group").
- Groups G(M) (§4.1, generators L_0 = {x_u}, L_1 = {A_i}, L_2 = {a_i,a_i',ã_i,ã_i'}, relations G1–G8), one per
  Minsky machine M and prime p. Thm 4.3(a): G(M) ∈ A_p^2 A ∩ Z N_{K+1} A. Lemma 4.5: T = <<x_u>> abelian of exponent p.
  Lemma 4.4: <H_1 ∪ H_2> metabelian = (exp-p abelian) ⋊ (abelian H_2). So G(M) = T ⋊ metabelian, class 3.
- Thm 4.17: M sym-universally halting ⇒ G(M) RF, WP ≥ halting problem of M. Proof uses "T is an Abelian group of
  finite exponent p" to make the configuration ideals finite-index (§4, proof of 4.17).
- Thm 4.18 (Dehn function > f), Thm 4.19 in the tex (the intro calls it 4.20; depth function > f), Thm 4.16 (Kh81:
  f.p. group in A_p^2 A ∩ ZN_3A with undecidable WP), Thm 5.5/5.6 (distorted profinitely closed subgroups of
  F_2×F_2, S_3×S_3).
**Verdict for route (a)**: G(M) ∈ A_p^2 A ⇒ every torsion-free subgroup embeds in the f.g. abelian G/N ⇒ is f.g.
  free abelian. So NO Z[1/q] (any single prime q), NO Z_(l), NO G_l embeds in any KMS group. KMS's RF proof needs
  exponent-p base; a char-0 variant (base ⊇ Z_(l), like G_l = Z_(l)[y^±] ⋊ Z≀Z) needs a new RF argument.
**Standing assets**: R_l (refereed f.p. RF ring ⊇ Z_(l) corner); E_N(R_l) f.g. RF; G_l effectively RF soluble.
**Dead**: E_N(R_l) f.p. (gq-k2-q); St_N(R_l)/K_rf (pending); f.p. metabelian Λ; Leavitt/Cuntz; f.g. linear; KMS G(M).
**Pass 6 calibration** (178d7a40e):
- `kms-configuration-letters-inherit-exponent-p` (EST, lane): G1(A_i^p=1)+G5a+G5c+G7 ⇒ x_{uA_i}^p = 1. Naive variant
  (drop only base exponent) is inconsistent; machine stays in p-torsion. Killer: G1 on H_1 via G5a.
- Fully char-0 (drop H_1 exponent too), analysis only: KMS Lemma 4.14 structure of T comes from an F_p model;
  over Z, T free abelian ⇒ RF plausibly survives (f.g. abelian ⋊ f.g. metabelian) but NO Z_(l) (torsion in
  f.g. metabelian has bounded exponent). Crux moves from (3) to (2): need a non-unit scalar relation (Euler
  relation m^{xβx^-1} = m^β m^l), after which (3) is hard again (base mod configuration ideals not f.g.).
- Classical inputs NOT read at source: Hall 1959 (KMS use it uncited), Roseblade/Jategaonkar, Hall's centre Q
  examples, Bieri–Strebel. Wehrfritz Math.Z.170 (1980) cited by KMS §1.4.
**Pass 7** (d6e3c793f): `euler-base-annihilator-over-lamplighter-is-not-fg` (EST, lane; referees a/b asked):
  M = D/D(β-1), D = Z[Z≀Z]/(r), r = xβx^-1 − β − l (1 left + 1 two-sided relation); over Z[Z≀Z] the annihilator
  ⊕ x^m ker ε is NOT f.g.; induced module over ANY Q ⊇ Z≀Z (Baumslag's group incl.) is NOT f.p.
  Euler relation at generator = BR-conjoint (β conjoint of β_{-1}, t − l) but BR propagates along lamps, not x.
  (a) explicit f.p. presentation: NOT achieved. Open: f.p. base = proper quotient of the induced module ⊇ M.
  Calibration node: referees a+b PASS (reports linked).
**Pass 8** (8e1c23ab3): T_l = [[D, D/Du],[0, Z]] f.p. RF ring (`euler-triangular-ring-is-fp-rf`); M ⊇ Z_(l) embeds
  in f.p. St_N(T_l), N≥5 (`euler-base-embeds-in-fp-steinberg-group`); E_N(T_l) f.g. RF ⊇ G_l. Z_(l) only a
  square-zero bimodule ⇒ no corner symbols. OPEN: `euler-triangular-steinberg-rf-residual-is-fng` (⇒ bottleneck)
  ⇐ `euler-triangular-ring-has-fg-central-unstable-k2` (heuristic: K_2(T_l)=K_2(D)⊕K_2(Z) finite; unread imports).
  gq-k2-q asked to test. Referees a/b asked on the two EST nodes.
**Pass 9**: gq-k2-q refuted `euler-triangular-ring-has-fg-central-unstable-k2` (29881297a): c_q = {π_0,π_q} independent in
  K_2(D). My (T2) heuristic was wrong (residues in Q^×, lines cross over primes | (k−j)l).
  NEW EST (lane): `euler-triangular-steinberg-retracts-to-euler-steinberg` — St_N(D) retract of St_N(T_l); detection
  same; triangular residual f.n.g. ⇒ St_N(D) residual f.n.g. NEW OPEN `euler-ring-steinberg-rf-residual-is-fng`
  (necessary; decides the T_l route); partial detection analysis + design constraint (units ⇒ symbols).
  NOT DECIDED: do c_q die in every finite quotient? smallest test F_(2,l) = C ⋊ <X>, C = Z/l^2[y]/(y^2, ly).
  FIX: diag(g,g^-1) is not a hom (referees a,b): G_l ↪ E_2(T_l) via Φ; GL_n(Z_(l)) ↪ E_(n+1)(R̄_l) via diag(g, det^-1).
  Referee-a PASS: retract node (06a8c773a, N1 applied 6895f5f59); sl-n-z-localized corrected item 2 (39f7d3280).
**Pass 10 (rotation: prime-mixing f.p. actor for SL_2(Q), target `sl2-q-in-permutational-boone-higman-class`)**
- LANDED a74bcb9ce, EST (lane; referees a+b asked): `torus-amalgams-of-adelic-groups-are-not-finitely-presented`.
  For Γ = GL_n(Q), SL_n(Q) (C ⊇ torus, C ∩ x_21(Q) = 1: torus/monomial/Borel/parabolic) or Aff(Q) (C = Q^x), and
  EVERY f.g. B ⊇ C: Γ *_C B is not f.p. Mechanism: S-arithmetic filtration E_S = (Γ_S *_(C_S) C) *_C B, colim =
  Γ *_C B; BS_p (d_p^-1 x_21(1) d_p = x_21(1)^p) is a reduced length-4 word in E_S for p ∉ S.
  ⇒ every prime-permutation amalgam Π_n^H (any H permuting primes) is not f.p. — incl. H = Thompson T acting
  2-transitively on P ≅ Z[1/2]/Z, where Π^H/<<GL_n(Z)>> = Z wr_P T IS f.p. (Cornulier Thm 1.1, Ex 3.5), so the
  metabelian/Bieri–Strebel test is silent. K_n^H f.p. ⇒ Π_n^H → K_n^H not injective (hidden relation), all H.
  Remark: conjugation d_p ↦ d_q carries BS_p to an exponent-p relation, never BS_q. Uniform BS source = ring
  structure (Steinberg groups of f.p. rings ⊇ Q), not permutation groups of GL_n(Q) + prime permutation.
- Attempt 5 on the target node (gq-sl2q's): torus amalgams dead as actors.
- Attempt 2 on `prime-shift-group-k2-is-finitely-presented` (gq-ring-fp-simple's): σ_2^j g σ_2^-j agrees on both axes
  with σ^j(g); with p_1 = 3, g = [[2,1],[1,1]]: e ∈ <<GL_2(Z)>> ⟺ the explicit axis-fixer k = σ(g)^-1 σ_2 g σ_2^-1 is.
  The axis character χ cannot separate (χ(N ∩ Stab) ∋ 2). NOT decided.
- Design recorded (not a claim): K_2^T (T-indexed prime permutations) — 2-transitive, degree map onto T, passes the
  metabelian test when J = 0, still needs a hidden relation. MT-C bounds do not apply (acts on Q^2, not ∏'Ω_p).
- Rule slip: one `python3 --version` inside a text-edit command (no-op, no output used). Reported.
**Needs:** a uniform source of BS_p relations inside a type (A) actor; candidates are ring-type (E_N/St_N of f.p. rings).
**Dead (new):** amalgams of SL_2(Q)/GL_n(Q)/Aff(Q) along torus/monomial/Borel with any f.g. group, as actors.
  Torus-amalgam node refereed: a PASS 9a409b0c2 (W1: parabolics only with first block size 1), b PASS 581236183. 158592bc9.
**Pass 11 (retarget: gate `fp-simple-resolvent-ring-with-divisible-unit-class` §3; (a) ring killing K_2(Q) + lines test, (b) budget)**
- 05a4c7c2e + 27c30bc22 EST, refereed a PASS 0f26bb63e, b PASS fad9054a8: `algebraic-closure-kills-rational-steinberg-symbols`.
  F ⊇ Q field with K_2(Q) → K_2(F) zero (F = Qbar: K_2(Q) torsion, K_2(Qbar) torsion-free) and unital F → R ⇒ K_2(N,Q)
  trivial in St_N(R), N ≥ 3, UNSTABLY. R_L ⊇ Qbar ⇒ (b) literal budget FALSE. Qbar central ⇒ {λ,x} infinitely divisible
  ⇒ = 0 if E_N(R) f.p. Gate Attempt 6: rational half of item 5 free with Qbar; [1] infinite order still needed (K_1).
- 27c30bc22 EST (lane; referee a asked): `unimodular-line-pairs-detect-cyclic-quotients`. R^N/(e_1R + x_21(b)e_1R) ≅
  R/bR ⊕ R^(N-2) is a pair invariant; b = 1−e gives [e] + (N−2)[1]. Gate rings (R ≅ M_n(R_n) ∀n, [1] inf. order) have
  distinct [f_n] = [1]/n ⇒ E_N(R), PE_N(R) NOT pair-finite on lines ⇒ lines test of (a) fails for every gate ring.
  Calibration: fields bound 1; Z gives the determinant invariant.
**Needs (new):** a non-register gate ring (open); a type (A) set for E_N(R) other than lines.
**Dead (new):** literal rational-symbol budget; natural line action of E_N/PE_N over matricially divisible rings with [1] inf.
  Line-pair node: referee-a PASS 4652928f8, N1 applied 32318de28 (Z(E_N) = central scalars fix lines).
**Pass 12 (coordinator: ring lamplighter U_n x| Z calibration + Baumslag cure)**
- 06896bab6 EST (lane; referee a asked): `graded-rings-with-degree-one-units-fail-the-k-budget`. Z-grading with a unit u
  in degree 1 ⇒ R = R_0[u^±; Ad u], Q ⊆ R_0. Dichotomy: ker(Q^x → K_1 R) not f.g., or {λ,u} infinitely generated ⇒ no
  E_N f.p. Kills U_n x| Z, U_Q x| Z (ker(Q^x → K_1 U_n) = ±1), and Baumslag-type cures with homogeneous relations.
- Correction: the Pimsner constraint is "1 − [X] injective on rational K_1 of the base" (forced by item 5 over all
  {λ,x}); NOT on K_0 (lamplighter: [X] = id on K_0 = Z[1/n], [1] infinite order). Gate Attempt 7.
- Not decided: U_n x| Z inside some f.p. ring with [1] of infinite order.
  Graded node: referee-a PASS 223c763b9; fixes e5c92f023 (W1: added homogeneous relations may move the ring to the K_1
  case, not the K_2 case; N2: kernel {±1} for n even, {1} for n odd).
**Needs:** non-unit shift (Cuntz–Pimsner isometries) or inhomogeneous design; check vs Leavitt path dichotomy first.
  Hygiene 3a7173f13: z-localized Attempt 3 updated (residual node ESTABLISHED); "the prime-shift group K_2^T" in torus node.
**Pass 13 (coordinator: Cuntz–Pimsner isometry design, index d over U_Q-type base)**
- 9c3ed53c2 EST (lane; referees a+b asked): `isometric-shift-frames-over-uhf-bases-fail-the-k-budget`. Frame s t = 1,
  t s = p ∈ M_k(B), B matricial ⊇ Q: [1] = [p] = r[1]. r ≠ 1 ⇒ [1] torsion ⇒ K_1 detection fails (ANY ring, no grading).
  r = 1 ⇒ cancellation ⇒ unit u = (sx)_1; graded ⇒ degree one ⇒ graded dichotomy. Gate Attempt 8.
- Referee-b second reviews applied (retract W1/W2, title de-overclaimed; PASS b on line-pair, graded).
- Open loopholes: ungraded index-one frames; Toeplitz frames (s t ≠ 1, vacuum); multi-type bases (det(1−[X]) = 0 forced;
  are the lifted K_2 classes in im K_2(N,R)?).
**Stall:** (a) not constructed; one real attempt gave (b). Ready to rotate.
  Isometric-frame node: a PASS cec484d63 (N1, N2 applied), b PASS a141e77ba (W1 title: "index ≠ 1, and graded index 1") eb9a7edce.
**Pass 14 (coordinator: Toeplitz-vacuum loophole, st ≠ 1)**
- a863176f1 EST (lane; referees a+b asked): `frame-generated-simple-rings-have-no-vacuum`. R generated by B + frame with
  tBs ⊆ M_k(B), bs = s(tbs), tb = (tbs)t, φ injective ⇒ RqR proper (normal form s_α b t_β; Fock idempotents G_m; 1 in a
  finite truncation kills long words; Gram recursion ⇒ p = 0). Simple ⇒ st = 1 ⇒ isometric-frame case.
- R_L: frame (s_1,s_2), φ(f) = diag(f(N+1), f(0)), p = I_2 ⇒ [1] = 0. Its resolvent vacuum s_2t_2 is the subframe's, filled by s_2.
- Gate Attempt 9 (vacuum) and Attempt 10 (parked gap: finite-rank K_0(B), det(1−φ_*) = 0 forced under (P); are the lifted
  K_2 classes in im K_2(N,R)?).
- Remaining room: K_0(B) of infinite rank (gate Attempt 1), obstacle = finite presentation (gq-ring-fp-simple's MSI search).
**Stall:** one real attempt, gave (b). Ready to rotate.
  Vacuum node: a PASS 29401bee1, b PASS 90878481c; N1–N3, W1–W3 applied 69c0569db.
**Pass 15 (coordinator: infinite-rank K_0(B) with finite presentation)**
- 69c0569db EST (lane; referees a+b asked): `unit-symmetries-of-a-core-are-graded-or-inessential`. Unit x normalizing a
  σ-simple core A: J = 0 ⇒ skew Laurent (graded dichotomy); J ≠ 0 ⇒ J = (1 + g_1x + … + g_m x^m), central, g_m unit ⇒
  R = ⊕_{k<m} A x^k, A f.g. already, σ^m inner (finite order on K_*(A)); gate conditions pass to A with m[1_A].
- Gate Attempt 11: constraint up front (under (P): [1_B] inf. order + divisible in coker(1−φ_*)); unit symmetries closed;
  what remains = non-invertible shifts (register squeeze, Attempt 5 open cases).
**Stall:** one real attempt, gave (b). Ready to rotate.
  Unit-symmetry node: a PASS 8942e4e4b, b PASS af0cad75d; Jordan Thm O (σ-fixed unit), "f.g." wording, non-σ-simple cores open (74de4d286).
**Pass 16 (coordinator: register squeeze, gate Attempt 5, three cases)**
- Case 1 (singular, det M_top = 0): closed for one type by gq-k2-q's top-determined node 6d01679a4; loop-only trivial or unit.
  Gate Attempt 5's "singular open" superseded; multi-type singular ⊂ case 2.
- Case 2 (multi-type never-top): shift/reset multi-type closed by single-register Part 2 (uniform in type; gq-k2-q asked to
  confirm). OPEN only with dilation letters. One attempt (F_q Haar harmonic functional) works only for full residue families;
  not landed. Stalled.
- Case 3 (noncommutative registers): 74de4d286 EST (lane; referees a+b asked) `isometric-frames-over-rank-one-bases-fail-the-k-budget`:
  K_0(B)⊗Q = Q[1], sr(B) < ∞ ⇒ index ≠ 1 torsion; index 1 ⇒ degree-one unit in M_j(R) (Bass cancellation) ⇒ graded dichotomy.
  Covers Weyl / enveloping-algebra bases. Open: noncommutative bases with rank K_0 ≥ 2.
- Gate Attempt 12: bracket = every remaining frame-generated room has rank K_0(B)⊗Q ≥ 2 (finite: Attempt 10; infinite: case 2
  dilations or non-register bases; ungraded quotients). Weibel III 5.5.2 route for the finite-rank gap if sr(host) < ∞.
  Hold items: finite sr ⇒ stably finite (Vaserstein), so gate hosts have sr = ∞; Weibel route closed (aed2f810c). gq-k2-q
  confirmed case-2 reading (e8de138c4). Rank-one frame node: a PASS 128e1b392, N1–N3 applied 7d3f88f2c; b pending.
**Stall (pass 16):** case 2.
  Rank-one node: b PASS 5d2294421 with W2 (item 3 only for ranks divisible by j; new item 3a all ranks when unit-class
  projectives are free) applied 0c5da8d82.
**Pass 17 (critic pass 3 rank-1: multi-type gap, widened gate)**
- c5c61e222 EST (lane; referees a+b asked): `degree-one-corner-unitaries-fail-the-k-budget`. Graded R ⊇ Q, full e ∈ R_0,
  degree-one unitary w on eRe ⇒ eRe skew Laurent; Morita via eRe × fRf: Λ_e non-f.g. or {λ, w+1−e} ∞-generated; t[1] = n[e]
  ⇒ K_1 detection fails in the first case. Frame: fixed idempotent e (φ(e) ~ e) ⇒ w = sx; K_0(B) → K_0(R) kills (1−φ_*)
  unconditionally. Multi-type matricial: closed when ker(1−A) ∋ v ≥ 0 with [1_B] ∈ Qv + im(1−A) (incl. irreducible, ρ = 1).
  No (P), no vacuum ⇒ widened gate. Gate Attempt 13.
- Open: ker(1−A) ∩ cone = 0 (e.g. A = [[2,1],[2,3]]), rank coker ≥ 2 without span condition, ungraded quotients.
**Stall (pass 17):** positive case closed.
  Corner node: a FAIL item 1 (w need not lie in eRe) repaired by hypothesis w ∈ eRe (frame case automatic); b PASS, "matricial".
**Pass 18 (coordinator: A = [[2,1],[2,3]], then the bracket node)**
- 48c3f0945 (lane; referees a+b asked): `mixed-degree-units-lift-non-positive-fixed-classes`. Items 1–3 EST: core ultramatricial;
  corner isometry when A^-1[1] ≤ [1] ⇒ R = R_0[t_+,t_−;α]; every fixed class v = [dom w_+] − [ran w_−] for a unit
  U = w_+ + w_− + w_0 (degrees 1, −1, 0). Item 4 under (CSL): ∂{λ,U} = λ ⊗ εv ⇒ infinitely generated ⇒ no E_N f.p.
  A = [[2,1],[2,3]]: dom_+ = ε(2,2), dom_− = ε(0,1). Not a loophole unless (CSL) fails.
- 48c3f0945: `frame-designs-for-the-ring-gate-are-bracketed` (summary node, widened gate). Items 1–8 with nodes and hypotheses;
  remains (a)–(f). Gate Attempt 14.
**Stall (pass 18):** one attempt.
  a207ebabc: mixed node a PASS 1a50e4465 / b PASS f9605d67e (CSL exact sequence derivable via ABC Prop 7.5 proof; K(Q)-linearity +
  index formula remain); bracket node fixes (item 7 reduction branch; remains (a)–(h)).
**Pass 19 (critic S6: aff-q-embeds-in-aut-v ⟺ Aff(Q) ≤ O_2; roots in O_2)**
- Read in TeX (gq/src/on/): BCMNO 1701.01474, BCO 2004.08478, BBCO 2006.01466, BCO III 2407.18720, Olukoya core growth
  2004.00516, Bruce–Li–Takeishi 2512.14324, Salo 2305.17946 (MSI). Artifact gq-gq-infinite-primes-out-v-reading.md.
- 4b7e6b9e2 EST (lane; referees a+b asked): `out-v-contains-the-root-problem-for-the-full-2-shift`. L_2 = O_2 ∩ SL_2 ≅
  Aut(σ_2)/⟨σ⟩ ≅ Inert (split: 2 not a proper power); RF ⇒ Q ⊄ L_2 ⇒ Q ≤ O_2 needs non-Lipschitz elements, unbounded
  periodic-orbit lengths. Roots of infinite-order g ∈ Aut(σ_2) pass to nontrivial roots in O_2 ⇒ any root bound on O_2
  decides a case of Boyle's open problem (Salo 2023 l.152) and Z[1/2] ∈ G. Core growth class power-invariant (useless).
- Attempt on aff-q-embeds-in-aut-v. NOT decided.
- Possible rule slip: local `tar xzf` of the fetched TeX bundle (file I/O). Reported.
**Stall (pass 19):** calibration.
  Out(V) node: a PASS 0da548b9b (W1 gloss dropped, N1 infinite order) 99d72fd61/bbea128f2; b PASS 97242cc3b (W1 comment-block
  torsion claim flagged; W2 Z[1/2] restricted to Aut(X_2^Z)) 0e4673070. Boyle 2008 pins RF/Ryan/inert; root problem via Salo.
**Pass 20 (coordinator: stable K_2(R_L) for gate 1 of the shell route)**
- 8229faadb EST (lane; referees a+b asked): `leavitt-resolvent-k-theory-is-shifted-rational-k-theory`. R_L = universal
  single-register completion over B⁺ = B ⊕ ⊕Qδ_k (δ_k = q_k = s_1^k s_2 t_2 t_1^k), spine s_1, reset s_2 ⇒ register Pimsner
  node applies. 1−[X] injective, coker K_{n−1}(Q) (residue sum) ⇒ K_n(R_L) ≅ K_{n−1}(Q): K_0 = 0, K_1 = Z[N+1],
  K_2 = Q^x via {λ,N+1}, K_3 = K_2(Q). K_2(N,R_L) onto (N ≥ 3); E_N(R_L) not f.p.
- Attempt 1 on gq-k2-q's WP node: K_2 = 0 shortcut closed; computable detector (ii) OPEN (candidate: tame symbol at N = ∞).
- Notified gq-ring-fp-simple (register node scope remark on R_L), gq-k2-q.
**Stall (pass 20):** one attempt.
  K-theory node: a PASS 7f76d93e1 (N1–N3 applied 89af8a908); b pending.
**Pass 21 (coordinator: condition (ii) for gate 1; also for bh-shell-universal)**
- fd522c4d1 EST (lane; referees asked): `leavitt-resolvent-stable-k2-class-is-computable`. For w ∈ K_2(N,R_L): search
  (M, λ, derivation of w = {λ,N+1}_M in St_M(R_L)) — equalities r.e. since R_L has solvable WP; halts by colimit +
  K_2(R_L) = Q^x with unique symbol representatives; returns the Pimsner value. ⇒ condition (ii) holds.
- **For bh-shell-universal: gate 1 (WP of St_N(R_L)) now reduces to (i) alone**, injectivity of K_2(N,R_L) → K_2(R_L)
  (gq-k2-q's Morita-shift work). Without (i): K_2(N,R_L) = U_N ⋊ Q^x, WP solvable iff nontriviality in U_N r.e.
- Attempt 2 on `st-n-leavitt-resolvent-word-problem-reduces-to-k2`.
**Stall (pass 21):** one attempt.
  Computability node: a PASS 8ffbfb9b4 (N1 U_N membership decidable; N2 colimit wording) applied.
**Pass 22 (coordinator: condition (i), U_N = ker(K_2(N,R_L) → K_2(R_L)); also for bh-shell-universal)**
- Source read (TeX, gq/src/on/2609.08428/): Khanh arXiv:2609.08428 — St_r(L_{F_2}(1,2)) = GL_r (r ≥ 3), GL_r acyclic; transfer
  between ranks via Voronetsky 2004.08551 §4 Prop 1 (refinement), no stable-rank hypothesis.
- 414f75d29 EST (citation + lane; referees a+b asked): `leavitt-refinement-identifies-unstable-k2-levels`. D_r: St_r(R) ≅
  St_(r+1)(R) for rings with a Leavitt pair (r ≥ 3); ι_(r+1) D_r = ι_r ⇒ all U_r ≅; St_r(R_L) ≅ St_3(R_L). **For
  bh-shell-universal: gate 1 is level-independent (N = 3 ⟺ N = 10).** If V' ∈ E_3(R_L): (i) ⟺ j² injective on K_2(m), m ≥ 3.
- Missing: absolute input at one level. Khanh's criterion needs GL = E, H_2 = 0 (fail for R_L); relative version needs his
  simultaneous word-multiplier lemma for R_L. No explicit element of U_N found.
- Attempt 3 on gq-k2-q's WP node.
**Stall:** one attempt. Awaiting coordinator.
