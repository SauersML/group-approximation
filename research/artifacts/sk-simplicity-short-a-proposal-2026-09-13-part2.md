# sk-simplicity-short-a: verification and the all-q version (part 2 of 2)

Lane sk-simplicity-short-a, 2026-09-13. UNREVIEWED. Part 1 holds the proposed text for the note.

Notation as in the note:
- R_q = LC(X,F_q) ⋊_T Z with (Tx)_n = x_{n+1} and u f u^{-1} = f∘T^{-1}, so u e_U u^{-1} = e_{TU};
- e_ij(r) = I_3 + rE_ij, [g,h] = ghg^{-1}h^{-1}, G = EL_3(R_q);
- (1) denotes the identities e_ij(r+s) = e_ij(r)e_ij(s) and [e_ik(r), e_kj(s)] = e_ij(rs) for i, j, k distinct.

## 1. Sentence-by-sentence check of the q = 2 text (part 1, section B)

**S1. Choice of w and 𝒫.**
- w exists because the entries are finite sums.
- For the partition, apply l.78-82 with L = 2w, refining the common refinement of the sets T^{-a}{f = 1}. Here f runs over the coefficients of the entries of g and g^{-1}, and |a| ≤ w.
- The levels T^aC, |a| ≤ w, are pairwise disjoint ⟺ C ∩ T^jC = ∅ for 0 < |j| ≤ 2w.
- f is constant on T^aC as soon as C ⊆ T^{-a}{f=1} or C ⊆ T^{-a}{f=0}.

**S2. Some h = e_ij(e_C) fails to commute with g.**
- Suppose g commutes with e_ij(e_C) for all i ≠ j and C ∈ 𝒫. The factors of e_ij(1) = ∏_C e_ij(e_C) commute by (1), so g commutes with E_ij for all i ≠ j.
- Comparing entries, g_{pi}δ_{jq} = δ_{pi}g_{jq}. So g_{pi} = 0 for p ≠ i and g_ii = g_jj, that is, g = cI_3 with c ∈ R invertible.
- Now e_ij(e_C) commutes with cI_3 iff ce_C = e_C c. Write c = Σ_{|j|≤w} c_j u^j. Then ce_C = Σ c_j e_{T^jC} u^j and e_C c = Σ c_j e_C u^j, so c_j(e_{T^jC} − e_C) = 0.
- For 0 < |j| ≤ w the sets C and T^jC are distinct levels, hence disjoint, and e_{T^jC} − e_C is nonzero at every point of C ∪ T^jC. So c_j vanishes there. Since 𝒫 covers X, c_j = 0.
- So c = c_0 ∈ LC(X,F_2). With c' = c^{-1} = Σ c'_j u^j, the u^0-coefficient of cc' = 1 is c·c'_0 = 1. So c(x) = 1 everywhere and g = I_3, a contradiction.
- Model test: over F_3 the constant function −1 is a nontrivial unit of LC(X,F_3). There the argument stops at g = cI_3 with c ∈ LC(X,F_3^×), which is why §2 adds the roots e_ij(e_C u). Over F_2 the argument is complete.

**S3. Tower subring.**
- ε_ab ε_cd = e_{T^aC} u^{a−b} e_{T^cC} u^{c−d} = e_{T^aC ∩ T^{a−b+c}C} u^{a−b+c−d}.
- If b = c this is ε_ad. If b ≠ c then T^aC ∩ T^{a+(c−b)}C = T^a(C ∩ T^{c−b}C) = ∅, because 0 < |c−b| ≤ 2w.
- The ε_ab are nonzero, since C is nonempty. Nonzero matrix units are linearly independent: multiply a relation by ε_{a'a'} on the left and ε_{b'b'} on the right.
- So B ≅ M_{2w+1}(F_2), with unit e = Σ_a ε_aa = e_{∪_{|a|≤w} T^aC}.

**S4. Product formula.** Let |i|, |j| ≤ w, and let f = λ on T^iC and f' = λ' on C. Then
- f u^i e_C f' u^j = λ' f u^i e_C u^j = λ' f e_{T^iC} u^{i+j} = λλ' e_{T^iC} u^{i+j} = λλ' ε_{i,−j};
- the indices check: a = i and a − b = i + j give b = −j, and |b| ≤ w.

**S5. y ∈ M_3(B).**
- ghg^{-1} = I_3 + g(e_C E_ij)g^{-1} and h = I_3 + e_C E_ij, so y = g e_C E_ij g^{-1} − e_C E_ij.
- The (p,q) entry of g e_C E_ij g^{-1} is g_{pi} e_C (g^{-1})_{jq}.
- Expand g_{pi} = Σ f_{i'} u^{i'} and (g^{-1})_{jq} = Σ f'_{j'} u^{j'}. By the choice of 𝒫, f_{i'} is constant on T^{i'}C and f'_{j'} is constant on C. So each term is a multiple of ε_{i',−j'} by S4.
- Also e_C E_ij = ε_00 E_ij ∈ M_3(B).

**S6. k − I_3 and k^{-1} − I_3.**
- Over F_2, h^{-1} = e_ij(−e_C) = h and h² = I_3.
- k = ghg^{-1}h, so k − I_3 = ghg^{-1}h − hh = yh.
- k^{-1} = hghg^{-1}, so k^{-1} − I_3 = hghg^{-1} − hh = hy.
- Both lie in M_3(B), because h = I_3 + ε_00 E_ij and M_3(B) is closed under products.

**S7. k ∈ H.**
- Put X = k − I_3 and X' = k^{-1} − I_3. From (I_3+X)(I_3+X') = I_3 we get X + X' + XX' = 0.
- With x = eI_3 + X and x' = eI_3 + X', and eI_3 the unit of M_3(B): xx' = eI_3 + X + X' + XX' = eI_3. Likewise x'x = eI_3.
- k = (1−e)I_3 + x.
- (1−e)b = b(1−e) = 0 for b ∈ B, so x ↦ (1−e)I_3 + x is a group isomorphism GL_3(B) → H.
- M_3(B) ≅ M_d(F_2), with d = 3(2w+1).

**S8. H ⊆ G.**
- M_3(B) ≅ M_d(F_2) sends ε_ab E_pq to the matrix unit at ((p,a),(q,b)).
- In H, the transvection t_{αβ}, for α = (p,a) ≠ β = (q,b), is (1−e)I_3 + eI_3 + ε_ab E_pq = I_3 + ε_ab E_pq.
- If p ≠ q, it equals e_pq(ε_ab).
- If p = q, then a ≠ b. Take r ≠ p and γ = (r,a). Then α, γ, β are distinct, and [t_{αγ}, t_{γβ}] = t_{αβ} holds in GL_d(F_2), by (1) for d×d matrices. It transfers to H through the isomorphism. So t_{αβ} = [e_pr(ε_aa), e_rp(ε_ab)].
  - Direct check in GL_3(R): ε_aa ε_ab = ε_ab and ε_ab ε_aa = 0. This is the note's l.212 identity with a different third column.
- Transvections generate SL_d(F_2) = GL_d(F_2).

**S9. H ⊆ N.**
- det takes values in F_2^× = {1}, so GL_d(F_2) = SL_d(F_2). Its centre consists of the scalars λ with λ^d = 1, and over F_2 that is only 1.
- PSL_d(F_2) is simple for d ≥ 3 (Jordan–Dickson), and d = 3(2w+1) ≥ 3.
- N ∩ H is normal in H because H ⊆ G, and it contains k ≠ 1. So N ∩ H = H.
- e_pq(e_C) = t_{(p,0),(q,0)} ∈ H ⊆ N.

**S10. Level ideal.**
- e_pq(r+s) = e_pq(r)e_pq(s), so J is additive.
- Let r ∈ J, s ∈ R, p ≠ q, and l ∉ {p,q}.
  - [e_pl(s), e_lq(r)] = e_pq(sr) by (1). It lies in N because e_lq(r) ∈ N and N ⊴ G.
  - [e_pl(r), e_lq(s)] = e_pq(rs) lies in N because e_pl(r) ∈ N.
- So J is a two-sided ideal. It contains e_C ≠ 0, and R is simple (l.104-109), so J = R. The e_pq(r) generate G, so N = G.

**Consequence.** G is nonabelian (e_12(1) and e_21(1) do not commute) and simple, so Z(G) = 1. The note never uses Z(G) otherwise.

**n ≥ 3.** The text works verbatim for EL_n(R_2), with d = n(2w+1) and "l a third index".

## 2. The all-q version (for sk-coefficients and the Cairn route)
Setting: G = EL_3(R_q), N ⊴ G, g ∈ N ∖ Z(G), and w the propagation bound of g and g^{-1}. Choose 𝒫 so that:
- the levels T^aC, |a| ≤ w+2, are pairwise disjoint;
- every coefficient of every entry of g^{±1} is constant on T^aC for |a| ≤ w+1.

Put m = w+1, ε_ab = e_{T^aC}u^{a−b} for |a|, |b| ≤ m, and B = span_{F_q} ε_ab ≅ M_{2m+1}(F_q).

1. **Centre and a noncommuting root.** Suppose g commutes with e_ij(e_C) and e_ij(e_C u) for all C and all i ≠ j.
   - By S2, g = cI_3 with c ∈ LC(X,F_q).
   - g also commutes with e_ij(u) = ∏_C e_ij(e_C u), so cu = uc, that is c∘T^{-1} = c. By minimality c is a constant λ ∈ F_q^×.
   - So central elements lie in F_q^× I_3. A noncentral g fails to commute with some h = e_ij(s), where s ∈ {e_C, e_C u} = {ε_00, ε_{0,−1}}.
2. **k lies in a finite GL_d.**
   - Product formula: let f be constant on T^iC (|i| ≤ w), f' constant on T^bC (|b| ≤ 1), and |j| ≤ w. Then f u^i ε_{0b} f' u^j = f e_{T^iC} (f'∘T^{b−i}) u^{i−b+j} = f(T^iC) f'(T^bC) ε_{i,b−j}, with |b−j| ≤ m.
   - So y = g(sE_ij)g^{-1} − sE_ij ∈ M_3(B).
   - k = [g,h] ∈ N∖{1}, with k − I_3 = yh^{-1} and k^{-1} − I_3 = −hy.
   - So k ∈ H = (1−e)I_3 + GL_3(B) ≅ GL_d(F_q), with d = 3(2w+3) ≥ 9.
3. **SL_d inside G.** Let S ≅ SL_d(F_q) be the copy inside H. Its transvections are I_3 + λε_ab E_pq.
   - For p ≠ q these are roots e_pq(λε_ab).
   - For p = q they are [I_3 + λε_aa E_pr, I_3 + ε_ab E_rp] with r ≠ p.
   - So S ⊆ G.
4. **k not scalar in H.**
   - [k,S] ⊆ N ∩ S, and N ∩ S ⊴ S.
   - Suppose N ∩ S were central in S. Then s ↦ [k,s] would be a homomorphism S → Z(S), since [k,ss'] = [k,s]·s[k,s']s^{-1}. S is perfect, so the homomorphism is trivial and k centralizes S, which makes k scalar in H, a contradiction.
   - So N ∩ S is a noncentral normal subgroup of SL_d(F_q) with d ≥ 3. By simplicity of PSL_d(F_q), S ⊆ N, and e_pq(e_C) ∈ N for all p ≠ q.
5. **k scalar in H.**
   - Then k = cI_3 with c = 1 + (λ_0 − 1)e and λ_0 ≠ 1.
   - Take r = e_{T^mC}u^{-1}. Then crc^{-1} = c e_{T^mC} (c^{-1}∘T) u^{-1}.
   - On T^mC we have c = λ_0. For x ∈ T^mC, Tx lies in T^{m+1}C, which is outside the tower because the levels up to w+2 are disjoint, so c^{-1}(Tx) = 1.
   - So crc^{-1} = λ_0 r, and [k, e_pq(r)] = e_pq(crc^{-1} − r) = e_pq((λ_0−1)r) ∈ N, with r ≠ 0.
6. **Level ideal.** J from S10 is a nonzero two-sided ideal by step 4 or step 5, so J = R and N = G.
   - G/Z(G) is finitely generated, by item 1 of `minimal-subshift-algebra-is-simple-lef-ring`.
   - G is infinite, since e_12(LC(X,F_q)) is infinite.
   - A finite-index normal subgroup is not central, so it equals G. So G has no nontrivial finite quotient.

## 3. Alternatives considered
- **The note's version** (κ: U → GL_d, piece W, conjugation by κ_0) is forced only because the coefficients of g vary along U. One clause refining 𝒫 removes it.
- **Three root shapes plus Z(G) = 1** serve only to find a noncommuting h. Over F_2 the roots e_ij(e_C) suffice by S2. Over F_q one adds e_ij(e_C u) and the scalar case (§2.5).
- **Avoiding the simplicity of GL_d(F_2)** would mean extracting a transvection from k ∈ N ∩ H by further commutators. That reproves Jordan–Dickson at greater length, so citing it is shorter.
- **The stable-rank route** belongs to sk-stable-rank-a/b. If sr(R) ≤ 2 were known, a citation of the Bass–Vaserstein sandwich theorem could replace the section. But the reader would need a noncommutative normal-subgroup theorem and a stable-rank computation that the note does not otherwise carry. Not decided here.
- **Normal closure of one transvection, or generation of G by tower groups:** both still need S2–S9. Neither is shorter.
