# sk-review-1, part 9: normal-structure shortcuts (Stepanov via pair dependence; Preusser and Vaserstein)

- **Reviewer:** lane sk-referee-1 (a Claude Code agent; not human review).
- **Scope:** queue entries 31–34. Main tip at review fb00634f36.
- **Method:** the mathematics was re-derived by hand. Preusser was re-read on MSI. The Stepanov and Vaserstein imports were not re-read (bounded; see §4).

## 1. `amenable-crossed-products-meet-stepanov-condition-b` + `-proof` (sk-stable-rank-b): PASS
**Item 1 (pair dependence).**
- Følner step. |kF∖F| < |F|/|S| for k ∈ S. Since SF = ⋃_k kF ⊆ F ∪ ⋃_k(kF∖F), we get |SF| < 2|F| ✓.
- Constant cylinder. The finitely many locally constant functions f_k∘m and g_k∘m (k ∈ S, m ∈ SF) are all constant on some nonempty clopen U ✓.
- Computing p·r_ρ.
  - From u_γfu_γ^{-1} = f∘γ^{-1} we get fu_γ = u_γ(f∘γ). So f_ku_{kg}e_U = u_{kg}(f_k∘kg)e_U = c_{k,kg}u_{kg}e_U.
  - Hence p·r_ρ = Σ_{m∈SF}(Pρ)_m u_me_U ✓, and likewise q·r_σ.
- Dimension count. K^F × K^F → K^{SF} has 2|F| > |SF|, so there is a nonzero kernel vector ✓.
- Nonvanishing. The u_g-coefficient of r_ρ is ρ_g e_{gU}, and distinct g are distinct basis elements ✓.
- For Γ = Z, with S = [-w,w] and F = [0,2w]: |SF| = 4w+1 < 4w+2 ✓.
- Model test. A Leavitt family forces r = t_0(s_0r + s_1s) = 0 and s = 0, so item 1 fails there, as the node says ✓.

**Item 2 (condition (b) for I = 0).**
- α = (0,r,s,0,…)^T ≠ 0 and α_1 = 0.
- (aα)_1 = Σ_k a_{1k}α_k = a_12r + a_13s = 0.
- With b = 1 and i = j = 1 this matches Theorem 4.4(b) as quoted in `stepanov-linear-dependence-standard-normal-structure` ✓.

## 2. `amenable-crossed-product-gl-normal-structure-is-standard` + `-proof`: PASS (conditional on the Stepanov import as quoted)
- **Step 1.** R = LC(X,K)⋊Γ is the Steinberg algebra of Γ⋉X, which is Hausdorff and ample.
  - Minimal action ⇒ minimal groupoid.
  - Topologically free ⇒ effective: the interior of the isotropy bundle is the unit space.
  - So R is simple by the reviewed `steinberg-algebra-simple-iff-minimal-effective` ✓.
- **Step 2.** R is simple, so its only proper ideal is I = 0. There GL(n,R,0) and E(n,R,0) are both trivial, so (a) holds ✓.
- **Step 3.** Condition (b) comes from §1 ✓.
- **Step 4.** Theorem 4.4 gives the standard sandwich E(n,R,I) ≤ H ≤ C(n,R,I) with I ∈ {0,R}.
  - I = R gives H ⊇ E(n,R).
  - I = 0 gives H ≤ C(n,R,0) = Center(GL_n R) = Z(R)^×I_n. A matrix commuting with every e_ij(r) is scalar with central entry ✓.
- **Step 5.** A normal subgroup of E(n,R) is normalized by E(n,R). So EL_n(R)/Z is simple ✓.

**Condition.** The step "the normal structure is standard" means exactly this sandwich for every H normalized by E(n,R). This review relies on the import node's quotation of Theorem 4.4 and on its reading of p. 2152 (see §4).

## 3. Route `subshift-elementary-group-simple-stepanov-proof` (into `subshift-elementary-group-is-simple-modulo-centre`): PASS (same condition)
- Steps 1–3 are the case Γ = Z, K = F_q of §2, with simplicity and the centre taken from `minimal-subshift-algebra-is-simple-lef-ring` ✓.
- Step 4.
  - Z(G) ⊆ F_q^×I_3.
  - G is infinite and finitely generated.
  - A finite-index normal subgroup is not central, because G is infinite and Z(G) is finite ✓.
- The route uses no towers, no finite simple groups and no stable rank ✓.

**For the note (main's call, reader merits).** This route gives a very short simplicity section: R simple, a four-line Følner count for Z, and a citation of Stepanov's Theorem 4.4. The reader must then trust a noncommutative normal-structure theorem (Zap. POMI 1997) that the note does not prove. Elsewhere in this review the self-contained texts are 47–48 lines (short-b, v2).

## 4. `standard-normal-structure-makes-simple-ring-el-simple` + `-proof`, with the Preusser import (sk-stable-rank-a): PASS
**Preusser import, checked verbatim.** Source: arXiv:1912.11386v1, fetched on MSI and extracted with gs txtwrite (472 lines).
- Lines 47–51: "Theorem 3. Suppose that R is an exchange ring and n ≥ 3. Let H be a subgroup of GL_n(R). Then H is normalised by E_n(R) iff there is an ideal I ⊳ R such that E_n(R,I) ⊆ H ⊆ C_n(R,I). Moreover, the ideal I is uniquely determined." ✓
- Line 136: "C_n(R,I) := φ^{-1}(Center(GL_n(R/I)))" ✓

**Exchange case.** R is simple, so I ∈ {0,R}. C_n(R,0) = Center(GL_n R) = k^×I_n ✓.

**Stable-range case.**
- The centre is a field k, so its only maximal ideal is D = 0. Take S = {1} ⊂ k∖{0}.
- sr(R) ≤ n-1 is then Vaserstein's hypothesis, and statement (2) applies.
  - B = R gives H ⊇ [E_nR, E_nR] = E_nR, since e_ij(r) = [e_ik(r), e_kj(1)].
  - B = 0 gives H central ✓.

**Status of the claim.** For R_X both ring hypotheses (exchange, sr ≤ 2) are open, as the node says. So this claim does not by itself prove the note's theorem ✓.

**Bounded parts.**
- Stepanov's Theorem 4.4 and the meaning of "standard" were not re-read. The import quotes the page images; the PDF is on MSI at /projects/standard/hsiehph/sauer354/un-stepanov/stepanov.pdf.
- Vaserstein's statement (2) and Theorem 4 were not re-read either; that PDF is on MSI too.
- Before the note cites Stepanov for simplicity, sk-citations should re-read p. 2152.

## 5. Status
- No GAP and no FAIL.
- §§2–3 are conditional on the Stepanov import quotation.
- Queue entries 31–34 are done.
