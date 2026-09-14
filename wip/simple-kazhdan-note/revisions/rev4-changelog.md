# Revision 4 changelog (sk-editor-4, 2026-09-13)

**Base.** Main rev3 at 9047d0d3c9 (md5 274f19367f7f706b05c017af721c3884; identical to `sk/drafts/rev3-typeset.tex`): 618 lines, 7 pages.

**Deliverables.**
- `sk/drafts/rev4.tex`, concatenated from `rev4-partA..D.tex`: 773 lines, md5 d850b3796c60f14c1eb790ddd2eaef83.
- `sk/drafts/rev4-typeset.tex` (patch3.pl | order.pl): 771 lines, md5 cf078a7ff220a4ee1b485f3d4107633a.
- Earlier drafts kept: `rev4-v1.tex` (21:41, pre-gate, md5 eee41cb5…) and `rev4-v1-typeset.tex`.

**Compile.** MSI `/scratch.global/sauer354/sk/editor4/`, texlive/2025, pdflatex 3 passes, COPYFILE_DISABLE=1, md5 identical on both ends. Both files: **0 errors, 0 overfull, 0 undefined, 1 underfull (the Champetier bibitem), 8 pages.**

**Checks.**
- 46 cite keys = 46 bibitems; every label resolves.
- No Codex, OpenAI or Astra; no priority "first" (only ordinals and "online first").
- patch3.pl changes nothing of substance, since the draft is already in typeset style; order.pl reports "changed: NO".

**Not landed** (directive).

## 1. Structure, before and after

| rev3 | rev4 |
|---|---|
| intro: question, Theorem 1, method credits, lamplighter sentence | question + answer (S6); Theorem 1 (n ≥ 3); background (E1, E3, BG1); the idea (S1) + amenable twin (S2) + Stepanov/Matui credits; Theorem 2 (matricial engine); results paragraph |
| §1 proof for Z (ring, models, simplicity, Brown) | §1 proof of Theorem 2 for any minimal topologically free Λ: ring and (T); simplicity (one-page N1–N5); finite simple models through simplicity (sk-verify-9 S1); Brown's formulation with P2 |
| — | §2 proof of Theorem 1: Z-action, seam m, D_ℓ onto M_N(F_2), rev3's e_ij(1) clause; rev4.1 slot comment |
| §2 LEF groups: Ore overgroup, E_n models, substitution list, Wilson corollary | §3: credit paragraph (CFF, Kionke–Schesler question, Boone–Higman); Cor 3 (finite simple limits); Cor 4 (countable LEF host + iff + recursive presentations, with the PASSed examples); one proof (wreath-commutator isolation, Variant A host, view models onto M_{2^{|Q'_n|}}(F_2) through Theorem 2, inline Whitehead); [[T]]′ ≤ G_X; G2 credit; no decidable host; SL_3(Z) obstruction |
| §3 word problems (Turing degrees, continuum many groups) | §4 word problems (K1) + separable factors (P1, which replaces the continuum-of-groups clause) |
| §4 questions (2) | §5 questions: f.p. sofic (a-U9, "not LEF", E2, "every sofic infinite simple Kazhdan group LEF?"), sofic host, rigidity + O1 |

## 2. Applied, with sources

**Apply-now items.**
1. **Introduction.** sk-intro-writer Variant I, with sk-lit-background BG1 (Thom's group "not residually finite and so lacks the factorization property") and BG2 (`\cite{Kirchberg,Radulescu}`). Reordered per S6. Keys: Gromov87, Gromov99.
2. **EL_2.** Applied in v1, then removed per decision 96 (OUT). Theorem 1 keeps "for every n ≥ 3".
3. **One-page §1** (sk-simpler-onepage, N1–N5): seam m; H_V = (1−e)I_3 + GL_3(A_V); yy′ = y′y = eI_3; the proof ends before Brown; the density clause and credits are kept. It is now written for general Λ, as the proof of Theorem 2.
4. **Locators.** GPS 51–111; Kionke–Schesler "online first (2024)" + DOI + arXiv; `\cite{Stepin,VershikGordon}` + bibitem.
5. **Rev3 referee findings.**
   - Referee a: U1, U2, U3, U4 (Ω, Λ, ξ, σ_n, μ_k, ω introduced), U6′ (native in Theorem 2's proof), U7 (covariance display), U9.
   - Referee b: B1 (ClarkEdie Cor 4.6, Crossref metadata), U1–U4, U6, D1, D2, D3 (paragraph rewritten).
   - B2/U8 (Mal'cev): applied in v2, then moot once Cor 4 printed the exact PASSed statement without "every f.g. linear group".
   - S1: superseded by 71(d).

**Gates opened by main.**
- **G1 headline** (sk-strong-8/6): view models on Y_n = F_2^{Q'_n} onto full matrix algebras (sk-verify-9 §3.2–3.3). The expander repair uses option R1: Theorem 2's marking contains e_ij(1) (1 ∈ S), so the Kazhdan set of EL_3(F) maps onto it in both quotients. §2 keeps rev3's e_ij(1) = ∏_a e_ij(τ_a) clause (G1′).
- **G2 host** (universal-lef-host-b Theorem C + host-a A1/A2): Cor 4 prints Theorem C + A1 with their examples (f.p. RF groups; G_Y with recursive language). sk-verify-11 fixes: injectivity reason; "Every group as in the last statement"; `\cite[Theorem~4.21]{KMS}`; "as finite subsets lie in finite products".
- **G3 Theorem 2 engine** (sk-simpler-unify) with sk-verify-9 S1: onto maps; marked convergence through simplicity for every ω, so the nonvanishing lemma is gone; F1–F4 credits restored; "matricial" defined in the statement. MorseHedlund38 dropped, since N_ℓ → ∞ follows.
- **sk-lef-proof-compress Variant A** (sk-verify-13 part3 PASS). Adopted in §3's combined proof:
  - its host paragraph (the fixed-point equation for minimality and topological freeness);
  - the inline Whitehead identities;
  - its wreath commutator in place of Ore;
  - W1 ("well defined as |Q_k| divides m_k").
- **Port** (sk-verify-13 part3 P1). The overgroup is built once, for countable Γ, because the wreath identity replaces Ore inside the isolation step:
  - (f_jk, t_k) on Q_k × Z/m_k replace (α_jk, β_jk);
  - doubled regular actions, parity and the Ore bibitem are gone;
  - Variant A's separate f.g. overgroup paragraph is not needed.

  **This port is checked by hand here and not reviewed.** [f_q, t](x,i) = (q^i q^{−(i−1)} x, i) = (qx, i); at i = 0 this needs q^m = 1. The view models stay σ_n: Δ → Q'_n finite models of Δ, which gives maps multiplicative for large n (Theorem 2 in S1 form) and onto full matrix algebras.
- **P2** (sk-verify-10 §5): Kirchberg sentence verbatim.
- **P1** (sk-verify-10 §5, F1/F2): placed after the Grigorchuk–Medynets remark. Its first sentence ("The same count holds…") is dropped, because decision 96 removed the continuum-of-groups clause it refers to.
- **SL_3(Z) obstruction** (sk-sl3z-bandwidth; review-7 part4, review-8 N6): w ≥ 1; "lies in no G_X"; CFKP credited as the analogue, with no claim on their Questions 5.1–5.3. About 7 printed lines, since every step of the Krylov argument is kept.
- **S2** (sk-verify-13 part2): intro sentence + w_g paragraph, with the homomorphism/commutator clause.
- **Also:** S1, S6, S7, E1, E2 (`\cite[\S5]{AlekseevThom}`), E3, K1, K2, K4.
- **sk-prior-art-2:**
  - G1: CFF clause (arXiv form);
  - G2: rephrased so each claim is exact (Wilson+KS give one simple LEF host for f.p. RF groups; CFF puts Higman's universal f.p. group in a simple Kazhdan group);
  - G3–G5.
- **sk-answered-questions:** P1 (Kionke–Schesler's amenable question; Boone–Higman shape) and P2 (Rauzy Prop. 26 and the proof of Lemma 27).
- **sk-questions-section:** 1.3 + O1 (no Connes, no C*-simplicity question).

**Wording and letter adaptations** (reader-facing, no mathematical change).
- **Letters.** K; A_V and H_V (A is the alphabet); Λ, Ω, ξ; μ_k and σ_n; z; e_U; unit variable v in the inline Whitehead identity (a, b are Lemma A's generators).
- **S1.** "Periodic points give…" → "Periodic sequences approximating X give…".
- **E1.** "first finitely presented examples" → "some of which are finitely presented" (G5).
- **Length trims, no step dropped:** results paragraph; S2 paragraph; §2 last sentence; isolation ending; continued-fraction sentence.

## 3. Left out, and gated
- **Character rigidity:** OUT per decision 96 (a separate paper). A ~1-page version with N1–N4 was drafted and removed.
- **EL_2 (n ≥ 2):** OUT per decision 96.
- **Every finite field** (sk-general-statement d7ef2a68fd; sk-verify-13 part4 PASS-WITH-FIXES G1–G3): NOT added, for two reasons.
  - It costs about +20 lines, and rev4 is at 8 pp.
  - Its change 3 ("central iff scalar image") uses the nonvanishing lemma that S1 removed. Its "the proofs above apply" was written and reviewed against v1's architecture (Z-case simplicity, rank two).
  - Porting it to Theorem 2's S1 form needs a new change 3: simplicity of G/Z, applied through the ultraproduct over every ω. That text would need review.
  - A marked `% rev4.1 SLOT` comment sits at the end of §2.
- **Rank-3 converse sentence:** not added, for length.
- **C4 Camm/Clapham, CIOS Cor 2.7:** not verified at source. No sentence claims a continuum of (T) group factors is new.

## 4. Doubts for main
- **The wreath-commutator port** inside the isolation step (see §2, Port) is unreviewed.
- **Theorem 2 in S1 form.** The mathematics is PASSed (sk-verify-9 §5, sk-review-8 part3), but this note wording is unreviewed: marking with 1 ∈ S; φ_k(1) = I; "trivial in G ⇒ trivial in SL_{3N_k} for large k" through φ_k(0) = 0.
- **Locators in arXiv numbering only:** KS Thm 1.2, ClarkEdie Cor 4.6, CFF Thm 1.5. Ozawa p. 527 is confirmed only through Thom. The Rădulescu volume data is from zbMATH via sk-lit-locators.
- **Budget:** 8 pp now. See the final report for how full page 8 is.
