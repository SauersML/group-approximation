# sk-review-1, part 6: sk-proof-minimal-conceptual (two ring lemmas) and sk-cut-sentences M1-M5

- Reviewer: lane sk-referee-1, a Claude Code agent. This is not a human review.
- Queue entries 7 and 9. Main tip at review: 2ecb00968.

## 1. sk-proof-minimal-conceptual proposal (E1-E4, candidate l.65-201): PASS

### Lemma 2 (simplicity of EL_n over a simple ring with local annihilation), proof re-derived for every n ≥ 3 and every simple R
- **Some h.** The coefficients r such that g commutes with every e_ij(r) form a unital subring C_g, closed under sums and products by (eq:elementary). C_g ≠ R because g is noncentral.
  - S_F = {s : ∃ t ≠ 0, tFs = 0} generates R, so S_F ⊄ C_g, and some h = e_ij(s) with s ∈ S_F gives γ = [g,h] ≠ I ✓.
- **t(γ-I) = 0.**
  - γ-I = (ghg^{-1}-h)h^{-1}.
  - The (p,q) entry of ghg^{-1}-h is g_{pi} s (g^{-1})_{jq} - δ_{pi}δ_{jq}s. Left multiplication by t kills it, since t g_{pi} s = 0 and ts = 0 (1 ∈ F).
  - So tγ = tI and tγ^{-1} = tI ✓.
- **bat ≠ 0.** If bRt = 0, then bRtR = bR = 0, because RtR = R (R simple, t ≠ 0). That contradicts b ≠ 0 ✓.
- **η.**
  - The (p,q') entry of (atE_pl)γ^{-1} is a·(t(γ^{-1})_{lq'}) = aδ_{lq'}t, so (atE_pl)γ^{-1} = atE_pl.
  - (atE_pl)² = 0 since l ≠ p. So η = (I + γ·atE_pl)(I - atE_pl) = I + (γ-I)·atE_pl, and its (q,l) entry is bat ≠ 0 ✓.
- **η^{-1} in column l.** ηe_d = e_d for d ≠ l, hence η^{-1}e_d = e_d ✓.
- **[η,e_dm(1)] = e_dl(c).**
  - ηE_dm = E_dm (column d of η is e_d).
  - Row m of η^{-1} is e_m^T + c e_l^T, so E_dmη^{-1} = E_dm + cE_dl.
  - (I + E_dm + cE_dl)(I - E_dm) = I + cE_dl.
  - This includes the case m = l ✓.
- **Level ideal.**
  - Signed permutation matrices e_ij(1)e_ji(-1)e_ij(1) conjugate e_dl(c) to e_12(±c), so c ∈ I.
  - I is closed under negation and under two-sided multiplication (commutators with the third index) ✓.

### Lemma 1 (unital subring of an algebraic ultraproduct of finite rings ⇒ GL_n LEF)
- M_n(∏_ω Q_k) = ∏_ω M_n(Q_k), and units are units coordinatewise ω-almost everywhere.
- Pick representative sequences for a finite set. Each product relation, each inverse relation and each inequality holds for ω-almost every k, so one k realizes all of them ✓.

### Local annihilation for R ("Simplicity" subsection)
- e_W f_j u^j e_V = f_j e_{W ∩ T^jV} u^j = 0 for |j| ≤ L.
- W exists because X is infinite: the complement of a finite set is a nonempty open set, and it contains a nonempty clopen set. V exists by continuity of T^j.
- For V_i ⊆ V_x, e_W f e_{V_i} = e_W f e_{V_x} e_{V_i} = 0. So r = Σ_i e_{V_i} r writes every r as a sum of annihilated elements, and the hypothesis of Lemma 2 holds ✓.
- Z(G) = 1 makes G simple ✓.

### Finite models (ultraproduct form)
- φ is a unital ring homomorphism for ω-almost every k, and it is injective once N_k → ∞ ✓.
- Two inherited defects remain in the candidate's wording:
  - C1 = sk-referee-1 G1: "separated by a segment $w_k$" still reads as the gap between the occurrences. The segment must begin at the first occurrence.
  - C2 = sk-referee-1 G2: "evaluating its local rule along $y_k$" does not fix the index convention. The relation P_kD_k(f)P_k^{-1} = D_k(f∘T^{-1}) holds for D_k(f)δ_n = f(T^ny_k)δ_n.
- sk-lef-short Replacement B (review part 2) repairs both, and adopting it here costs nothing.

### Model tests (§ of the proposal)
- A field fails the hypothesis ✓.
- LC(X,F_2) satisfies it and is not simple, so simplicity of R is needed ✓.

### Optional notes
- C3. E3 cites `\cite[Lemma~4.3]{Stepanov}`. sk-citations should confirm the lemma number, since the proposal says it is still to be checked.
- C4. With E4 the old paragraph "We will also need that $R$ is simple ..." still ends "Thus $Z(G)=\{1\}$". It is used once, at the end of "Simplicity" ✓.
- C5. Lemma 2 needs n ≥ 3 only to have a third index d ∉ {m,l} and signed permutations. Both hold for n = 3 ✓.

## 2. sk-cut-sentences part 2, checks M1-M5 (queue entry 9): PASS
- **M1.** With [x,y] = x^{-1}y^{-1}xy: [e_ik(r), e_kj(s)] = e_ik(-r)e_kj(-s)e_ik(r)e_kj(s). That is the standard commutator of e_ik(-r) and e_kj(-s), which is e_ij(rs). So (eq:elementary) holds under both conventions ✓.
  - k ≠ 1 under either convention.
  - Over F_2 transvections are involutions, so the transvection identity is convention-free ✓.
- **M2 (C14).**
  - E_{0,-1}(U) = e_U u and E_{01}(U) = e_U u^{-1}, both in B_1(U) with U ∈ 𝒫.
  - Absorption into B_{w+1}(U) needs U∩T^jU = ∅ for 0<|j| ≤ 2w+2, which 𝒫 has ✓.
  - The translates in l.189-192 are unnecessary ✓.
- **M3 (C15).** For x = (p,a) and z = (p,b) with a ≠ b, take y = (q,b) with q ≠ p. Then t_xy = e_pq(E_ab(W)), t_yz = e_qp(E_bb(W)), and [t_xy, t_yz] = t_xz is the note's l.212 identity ✓.
  - The replacement sentence says "for distinct coordinates x, y, z" but does not name y. Adding "(take $y=(q,b)$ with $q\ne p$)" costs no line. Optional.
- **M4 (C9).** ✓
- **M5 (C19).** The interleaved real x = Σ_i (b_i 2^{-2i-1} + a_i 2^{-2i-2}) is irrational because its digit sequence contains the non-eventually-periodic sequence (b_i). Its expansion is unique. x computes A by reading alternate digits, and A computes x because (b_i) is computable ✓.
- C12, C13, C16, C17, C18: wording only, with no mathematics to check.

## 3. Status
No GAP and no FAIL. Queue entries 7 and 9 are done.
