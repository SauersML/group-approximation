# gq-ring-fp-simple
**Approach:** family rings. Current: char-0 ring Boone–Higman (coordinator target), register method on Leavitt–Nekrashevych completions.
**Established (refereed):**
- R_L f.p. simple char 0 ⊇ Q: PASS a (8f4edc918), b (dfd8468b9), c (f7c7c3e04). Toeplitz R_T, GL_n(Q) ≤ E_{n+1}(R_T), integral-form obstruction: PASS a (7bf46a046).
**Established (refereed PASS a 69a3cc64f, b d7414d7a4; fixes 0c0351c66):**
- `rational-function-fields-embed-in-fp-simple-rings`: Q(t_1..t_k) ⊆ explicit f.p. simple R_k (registers + one resolvent G = N+1+Σ(t_i−C_i)P_i).
- `char-zero-representable-rings-embed-in-fp-simple-rings`: every subring of M_D(C⊗Q<x>), C f.g. commutative Q-algebra or f.g. char-0 field ⇒ f.p. simple ring. Includes all f.g. subrings of M_n(F), F char 0.
- `field-envelopes-pass-to-algebraic-closures`: K ⊆ f.p. simple ⇒ K̄ ⊆ R ⊗ L_Q(1,2); every countable char-0 field of finite trdeg embeds; Q̄ ⊆ R_L.
- `fp-simple-q-algebras-embed-in-fp-simple-rings`: Z(R_L) = Q; for Q-algebras, envelopes over Z ⇔ over Q.
**Established (lane proof, referees requested 66b7264f4):** `fg-semiprime-pi-q-algebras-embed-in-fp-simple-rings` (f.g. semiprime PI Q-algebras, incl. semiprime GK ≤ 1, embed in simple rings f.p. over Z).
**Open:** `countable-char-zero-fields-embed-in-fp-simple-rings` (≡ Q(t_1,t_2,...)); `char-zero-ring-boone-higman` (≡ algebra BH at K = Q, route from that root).
**Refuted:** `leavitt-resolvent-derived-units-mod-centre-fp-simple` (90ff0b8ea, scalar commutators).
**Dead:** shift tape over Z[T_I] ⋊ F for Q(t_1,t_2,...) (tape f.p. OK; values are one-pass bounded-rank programs, miss generic polynomials; 66b7264f4). Toeplitz/Weyl vacuum (not simple); binary Leavitt + multiplicative counter (Z[1/2] only); registers over finitely many central transcendentals for infinite trdeg.
**Sparks:** Q(t_1,t_2,...) via e^{t^m} constants with D E_m = E_m D + m t^{m−1} E_m; char-p register variant needs base points over extensions (Artin–Schreier irreducibles vanish on F_p^k).

## 2026-09-18 — K_2 finite presentation (target 9)
- LANDED e7a442014: prime-shift-kn-fp-reduces-to-a-metabelian-quotient (+proof), ESTABLISHED lane proof, referees a and b requested.
  - Degree character d: K_n -> Z, from k(tw) = σ^d(t) k(w). Z(K_n^0) = scalars.
  - K_n/<<GL_n(Z)>> ≅ (Q_>0/I_n) ⋊ Z.
  - Bieri–Strebel: K_n fp ⇒ e ≡ one-sided product of p_k-dilations mod <<GL_n(Z)>>.
  - GL_n(Z)-trivial point germs are blind to e.
  - <GL_n(Z),2I,σ_n> is not fp.
- OPEN: prime-shift-group-k2-is-finitely-presented, with Attempt 1 (germs, content, pair-det/tree types, averaging, the A_1 copy, the presentation side).
- Stuck on deciding: needs either a GL_2(Z)-nontrivial invariant or a hidden relation (Dickson-type).
- 41bead898: K_n reduction nits applied. Referees a and b both PASS.

## 2026-09-18 — fp self-similar host for Γ_p / Z_(l) (target 10)
- LANDED dee7ac8ab. Referees a and b requested.
  - p-adic-dilation-normalizers-act-by-power-maps (+proof): a homeomorphism of Z_p, or a germ at 0, normalizing a rank-3 group of rational dilations acts by a rational power map (p-adic six exponentials). So no tree prime-shift; even a 3-step chain d_q0→d_q1→d_q2→d_q3 is impossible.
  - finite-state-mobius-pieces-see-finitely-many-primes (+proof): finite-state pieces are affine over one Z[1/N]; with the Baire lemma, <Γ_0, finite-state locally-Möbius h_i> sees finitely many primes. Useful finite-state generators must be wild.
  - Attempt 5 on rational-iwahori-group-lies-in-fp-self-similar-group. f.g. reduction: an automaton group W ∋ all d_q gives a f.g. self-similar overgroup <Γ_p(1), W>.
  - Attempt 2 on euler-lamplighter-has-a-faithful-finite-state-action: l-adic closure conditions.
- Stuck: no construction of wild finite-state generators producing infinitely many d_q; fp not reached.
- fd9d196ca: referee fixes on the two self-similar obstruction nodes (both PASS; Serre DPP 1965/66 exp. 15 Thm 1 pinned).

## 2026-09-18 — K_∞ (target 11, parked)
- 2d7c98291 + 476938cdb: k-infinity-lies-in-a-simple-localization-of-an-fp-ring. Baumslag-type tape Z[t_v] ⋊ Z^2 is fp; K_∞ ⋊ Z^2 is simple. No f.g. subring of Frac(P) ⋊ G (G degree-preserving) contains Frac(P). Referees a and b PASS, fixes applied.
- Attempts 4 and 5 on countable-char-zero-fields-embed-in-fp-simple-rings (2d7c98291, 14b0879dc): register designs; units commuting with registers force t = utu^-1; single-twist tapes are one-pass; the algebraic streaming lower bound.

## 2026-09-18 — K_2 membership (target 12, stalled)
- 2a21b34d8: Attempt 3 on prime-shift-group-k2-is-finitely-presented.
  - k halves the antidiagonal.
  - The family n = σ^j(g)^-1 σ_2^j g σ_2^-j, g = [[a,a-1],[1,1]], has χ_3 = 1/D.
  - The S_3 symmetrization reduces e ∈ N to a three-line pointwise fixer r.
  - No scalar formula on those three lines separates. Stalled.
- 2af1a6a8e: Attempt 4, a bounded MSI search for the hidden relation (~16 min compute). Nothing is left running.
  - No linear relation with |det| != 1 and no r-translated match.
  - Covered: |j|≤1 to length 5 (length 6 partial, 1.64M elements); |j|≤2 and wide shears to length 4.
  - Calibrated; the independent sympy verifier passes its controls.
  - Artifact: gq-ring-fp-simple-k2-hidden-relation-search.md. Stopped at budget.
- 6a8d87fb1: CORRECTION. The Attempt 4 search was structurally blind: every σ_2^j GL_2(Z) σ_2^-j word preserves content, so both tests are vacuous.
  - Attempt 5: N = <σ_2^j SL_2(Q) σ_2^-j, D>.
  - The tabulation shows near misses keep content (ratio 1) and no extra line, while r doubles content on (1,1).
  - Content can't separate r from N, since SL_2(Q) ⊆ N changes content. Stalled.
  - The informative search would use σ_2^j x_12(q) σ_2^-j with rational q; not run.
- 62701057b: Attempt 6, the rational-shear search (~25 min MSI; nothing left running). No hits.
  - Generators σ_2^j x(q) σ_2^-j, q ∈ {±1,±2,±1/2[,±3,±1/3]}, |j| ≤ 2; length 3 complete, length 4 partial.
  - The blindness pre-check passed: no known invariant separates r from the searched group.
  - The planted calibration inside the group recovered 39/39.
