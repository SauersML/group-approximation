# sk-review-1, part 5: sk-proof-minimal-concrete v2 (tower-free extraction) and the indicator-ideal node

- **Reviewer:** lane sk-referee-1 (a Claude Code agent; not human review).
- **Queue entries:** 12 and 10. Main tip at review 4ef4add917.
- **Method:** every identity re-derived by hand.

## 1. sk-proof-minimal-concrete part 3, v2 (replaces l.67-227; 105 source lines): PASS
The "Ring and property (T)" and "Finite models" subsections are those of v1 (review part 3 §1), so their verdicts and notes C2–C5 carry over. New in v2 is the Simplicity subsection, checked below.

**Ring simplicity and centre.** This is the note's argument l.104-113, compressed ✓. "T has no periodic points" now comes before it is used, which resolves note C1.

**Choice of 𝒫 and W_C.**
- X is infinite, so the complement of the finite set {T^jx : |j| ≤ w} is a nonempty open set, and it contains a nonempty clopen W.
- T^jx ∉ W for each |j| ≤ w, so continuity of T^j gives a clopen V ∋ x with T^jV∩W = ∅.
- A finite subcover and its refinement with the letter partition are pieces C ⊆ V_x, and they inherit W_C ✓.

**Noncommuting h.** Unchanged from v1 ✓. It uses Z(R) = F_2.

**Local annihilation.**
- For an entry f = Σ_{|j|≤w} f_ju^j of g and s ∈ {e_C, e_Cu}: t f s = Σ_j f_j e_{W_C}e_{T^jC}u^j(1 or u) = 0, because W_C∩T^jC = ∅. The case f = 1 is j = 0 ✓.
- Only the entries of g are needed, not those of g^{-1}.
  - (tgS)_{pq} = t g_{pi} s δ_{jq} = 0, so t·gSg^{-1} = 0.
  - Also tS = 0.
  - With h^{±1} = I_3+S (characteristic 2, S² = 0): t(γ-I_3) = t(gSg^{-1}-S)(I_3+S) = 0, so tγ^{-1} = tI_3 ✓.
- A nonzero a-factor exists. If bRt = 0, then RbRt = 0. R is simple and b ≠ 0, so RbR = R and t = 0, contradicting W_C ≠ ∅ ✓.

**η = [γ, e_pl(at)].**
- At γ^{-1} = atI_3 entrywise: (at E_pl)γ^{-1} has (p,q') entry at(γ^{-1})_{lq'} = aδ_{lq'}t. So γ e_pl(at)γ^{-1} = I_3 + γ·(atE_pl).
- Multiply on the right by I_3 - atE_pl. Here (γ·atE_pl)(atE_pl) = 0, because the first factor is supported in column l ≠ p.
- So η = I_3 + (γ-I_3)·atE_pl, supported in column l, with (q,l) entry bat ≠ 0 ✓. And η ∈ N ✓.

**η^{-1}.** η^{-1}-I_3 = -η^{-1}(η-I_3). Left multiplication keeps the column support, and η ≠ I_3, so some entry c at (m,l) is nonzero ✓.

**[η, e_dm(1)] = e_dl(c) for d ∉ {m,l}.**
- Column d of η is e_d, so ηE_dm = E_dm.
- Row m of η^{-1} is e_m^T + c e_l^T. So E_dmη^{-1} = E_dm + cE_dl. This also holds when m = l.
- (I_3 + E_dm + cE_dl)(I_3 - E_dm) = I_3 + cE_dl, using E_dmE_dm = 0 (d ≠ m) and E_dlE_dm = 0 (l ≠ d) ✓. Such a d exists for n = 3 ✓.

**Every position.**
- The five commutators in check 7 are the second identity of (eq:elementary) with distinct indices, and each has one factor in N ✓.
- I_N is a two-sided ideal and contains c ≠ 0, so I_N = R ✓.

**What v2 uses.**
- Simplicity of R (twice) and Z(R) = F_2, both proved in its first paragraph.
- It does not use the simplicity of GL_d(F_2), towers, absorption, or LC(C, GL_d).

**Optional notes.**
- V1. "then $a\in R$ with $bat\ne0$, which exists because $R$ is simple": the one-clause reason "(otherwise $RbRt=0$)" helps.
- V2. "$(\gamma-I_3)\,at\,E_{pl}$" is a matrix product. Its entries are (γ-I_3)_{q'p}·at, and the order of these noncommuting factors matters; writing "the matrix $(\gamma-I_3)(atE_{pl})$" removes any doubt.
- V3. As the lane says, abstract l.32-33 and intro l.58-62 describe the tower commutator and go stale under v2.

## 2. `subshift-f2-ring-indicator-ideals-and-centreless-el3` + `-proof` (sk-cut-structure): PASS
**(1) Indicator ideals.**
- e_{T^nW} = u^ne_Wu^{-n} ∈ I.
- Every orbit is dense, so the translates cover X, and compactness gives a finite subcover.
- 1 - ∏_i(1-e_{T^{n_i}W}) is a sum of products each containing some e_{T^{n_i}W}. The product is 0, so 1 ∈ I ✓.

**(2) Z(EL_3(R)) = 1.**
- A central g commutes with E_ij for all i ≠ j, so g = cI_3.
- From ce_V = e_Vc: the u^j coefficient of e_Vc - ce_V at x is f_j(x)(1_V(x) - 1_V(T^{-j}x)). A clopen V separating x from T^{-j}x kills f_j for j ≠ 0.
- Then f_0g_0 = 1 forces f_0 = 1 ✓.

**Wording note.** The claim says "Minimality is not used" in (2). The route justifies "T has no periodic points" by "a finite orbit would be a proper closed invariant set", which is minimality. The statement is true if aperiodicity is the hypothesis. Suggest "(2) uses only that $T$ has no periodic points" and drop "Minimality is not used", or state (2) for aperiodic subshifts.

## 3. Status of the simplicity texts for revision 1 (all PASS)
| text | simplicity uses | length of the proof section l.67-227 |
|---|---|---|
| frozen note | R simple, Z(R), towers, κ, GL_d(F_2) simple | 161 |
| minimal-concrete v1 (part 2) | Z(R), towers, GL_d(F_2) simple, covering | 119 |
| minimal-concrete v2 (part 3) | R simple, Z(R), local annihilation, no towers, no GL_d | 105 |
| short-a q=2 text + v1 rings/LEF | R simple (or covering), constant towers, GL_d(F_2) simple | ≈ 161-27-7 |
| short-b §3 | covering, constant small sets, GL_d(F_2) simple, no Z(R) | 161-47 ≈ 114 |

- v2 is the shortest whole-section text. short-b is the shortest simplicity section that needs no ring lemma.
- The F_q warning of part 4 applies to short-a and short-b, which use LC(X,F_2)^× = {1}. It also applies to v2 in one place: "c ∈ Z(R)^× = {1}" uses F_2 as well. Over F_q, v2's extraction goes through with Z(G) ⊆ F_q^×I_3, and the level ideal needs no scalar case.
