# sk-el2, part 2: EL_2 over every minimal subshift algebra is simple, Kazhdan and LEF

Lane sk-el2, 2026-09-13. Status: UNREVIEWED (queued with sk-verify-4). This part uses Theorem A from part 1 and
main's reviewed import `minimal-subshift-algebra-is-simple-lef-ring`.

## 1. Theorem B

**Theorem B.** Let X be an infinite minimal subshift, q a prime power, and R = LC(X,F_q) ⋊_T Z.
1. EL_2(R) is infinite, finitely generated, and has property (T).
2. For q = 2, EL_2(R) is simple (so its centre is trivial) and LEF, hence sofic and hyperlinear.

So the note's theorem holds for EL_n with every n ≥ 2. This answers `el-2-over-every-minimal-subshift-algebra-is-kazhdan`
positively, Sturmian X included.

**Proof of 1.**
- *(T).* R is finitely generated (import item 1). Take a clopen W with ∅ ≠ W ≠ X, and put e = e_W, e' = e_(X∖W).
  - By minimality and compactness, finitely many translates T^aW cover X, and e_(T^aW) = u^a e u^−a.
  - So 1 = 1 − Π_i(1 − e_(T^(a_i)W)) ∈ ReR. The same argument gives R e' R = R.
  - Theorem A (part 1) gives property (T).
- *Infinite.* EL_2(R) contains e_12(LC(X,F_q)).
- *Finitely generated.* A countable discrete group with property (T) is finitely generated (Bekka–de la Harpe–Valette,
  *Kazhdan's property (T)*, Thm 1.3.1; recalled, not re-read).

**Proof of 2 (LEF).**
- Import item 3: R embeds unitally in an algebraic ultraproduct of matrix algebras over F_2.
- So every finitely generated subgroup of GL_2(R) is LEF (the import's consequence), in particular EL_2(R).
- The note's finite models with 2m_ℓ in place of 3m_ℓ show the same directly.

**Proof of 2 (simplicity), q = 2.** Let G = EL_2(R), 1 ≠ N ⊴ G and 1 ≠ g ∈ N.
- Let w ≥ 1 bound the absolute values of the exponents of u in the entries of g and g⁻¹. Choosing w ≥ 1 is allowed.
- As in the note, call a clopen V *small* if (a) V ∩ T^jV = ∅ for 0 < |j| ≤ 2w, and (b) f∘T^i is constant on V for
  every |i| ≤ w and every coefficient f of an entry of g^{±1}.
- T has no periodic points, so every clopen set is a finite disjoint union of small ones.

*Step 1: a noncommuting root element.*
- Suppose g commuted with e_12(e_V) and e_21(e_V) for every small V. By additivity it would commute with them for
  every clopen V, including V = X.
- Then g commutes with E_12 and E_21, so g = cI_2 with c = Σ_j c_j u^j ∈ R.
- For every clopen V, e_Vc − ce_V = Σ_j c_j(e_V − e_(T^jV))u^j = 0. Choosing V ∋ x with T^−jx ∉ V gives c_j(x) = 0 for
  j ≠ 0. So c ∈ LC(X,F_2).
- Comparing constant coefficients in cc⁻¹ = 1 shows c is a unit of LC(X,F_2), so c = 1 and g = 1, a contradiction.
- So some h ∈ {e_12(e_V), e_21(e_V)}, with V small, does not commute with g.

*Step 2: a finite simple subgroup of N* (the note's argument with n = 2).
- Put ε_ab = e_(T^aV) u^(a−b) for |a|,|b| ≤ w. Condition (a) gives ε_ab ε_a'b' = δ_(b a') ε_ab'.
- With d = 2(2w+1) ≥ 6 and coordinates (p,a), p ∈ {1,2}, the map ψ(E_((p,a),(q,b))) = ε_ab E_pq is an injective
  multiplicative linear map M_d(F_2) → M_2(R). A ↦ I_2 − ψ(I_d) + ψ(A) embeds GL_d(F_2) in GL_2(R); call its image H.
- *H ⊆ G.* A transvection between (p,a) and (q,b) maps to e_pq(ε_ab) when p ≠ q. When p = q it is the commutator of the
  transvections (p,a)→(p',a) and (p',a)→(p,b), with p' ≠ p.
- *k ∈ H.* Put k = [g,h] ∈ N∖{1}.
  - Condition (b) gives f u^a e_V f'u^b = f e_(T^aV)(f'∘T^−a) u^(a+b) ∈ {0, ε_(a,−b)}.
  - So k − I = (ghg⁻¹ − h)h and k⁻¹ − I = h(ghg⁻¹ − h) lie in ψ(M_d(F_2)), and k ∈ H.
- *Conclusion.* H ≅ GL_d(F_2) = PSL_d(F_2) is simple and N ∩ H ∋ k is nontrivial, so H ⊆ N. In particular
  e_12(e_V) ∈ N.

*Step 3: the level through three Peirce blocks.*
- Put e = e_V and e' = e_(X∖V). Both are full, as in the proof of 1; V ≠ X by (a), since w ≥ 1.
- Use part 1's notation: M = M_2(R), E_1 = eE_11, E_2 = eE_22, E_3 = e'I_2, and Y_AB = I_2 + E_AME_B. Each E_A is
  full in M.
- For A ≠ B put J_AB = {x ∈ E_AME_B : I+x ∈ N}. It is an additive subgroup, because Y_AB is abelian.
- *Propagation.* Let A, B, C be distinct. For x ∈ J_AB and y ∈ E_BME_C, yx = 0, so Lemma 1 gives
  [I+x, I+y] = I+xy ∈ N. For z ∈ E_CME_A, xz = 0, so [I+z, I+x] = I+zx ∈ N. Hence
  J_AB · E_BME_C ⊆ J_AC and E_CME_A · J_AB ⊆ J_CB.
- *The chain.* It starts at x_0 = e_VE_12 = E_1x_0E_2 ∈ J_12.
  - J_13 ⊇ x_0E_2ME_3 = e_VE_12Me' = {[[e_V m_21 e', e_V m_22 e'],[0,0]]} = E_1ME_3.
  - J_12 ⊇ J_13·E_3ME_2 = E_1ME_2 (E_3 full).
  - J_32 ⊇ E_3ME_1·J_12 = E_3ME_2 (E_1 full).
  - J_31 ⊇ J_32·E_2ME_1 = E_3ME_1 (E_2 full).
  - J_23 ⊇ E_2ME_1·J_13 = E_2ME_3.
  - J_21 ⊇ J_23·E_3ME_1 = E_2ME_1.
- So every Y_AB ⊆ N. By part 1 Lemma 2(ii) they generate G, so N = G.
- The centre is a normal subgroup other than G, because G is not abelian, so it is trivial. ∎

## 2. Scope and firewalls
- **F_q, q > 2.** Theorem B(1) holds, (T) included. The simplicity proof above does NOT transfer verbatim.
  - Step 1 uses LC(X,F_2)^× = {1}. Over F_q a nonconstant unit c commutes with every e_ij(e_V) (sk-referee-1's
    warning, main's rev2 decision 23).
  - Step 2 would need SL_d and a non-scalar κ.
  - So simplicity of EL_2(R)/Z for q > 2 is not claimed here.
- **Never write "n = 2 loses (T)"** for subshift algebras. It fails for every infinite minimal X.
- **Rank one, EL_2 without idempotents.** EJZK's footnote: EL_2(R) lacks (T) when R surjects onto Z or F[t], or R is
  infinite commutative. Theorem A's hypothesis excludes both cases (part 1 §2).
- **Subsumes** `cyclic-factor-subshift-el-2-is-simple-kazhdan-lef` for (T) and q = 2 simplicity, with no finite
  cyclic factor needed. That node's Morita reduction also gives simplicity mod centre over every F_q in its case.
- **n ≥ 3.** Nothing changes: the note's proof uses EJZ directly.

## 3. Model tests of Theorem B
- *Finite X.* Hypothesis fails: T has a periodic point, and R maps onto M_p(F_2[t^±1]). EL_2 surjects onto
  EL_2(F_2[t^±1]), which lacks (T), consistent with the need for infinite X.
- *Non-minimal X without periodic points.* Theorem A still gives (T) when W is chosen with e_W and 1−e_W full,
  e.g. if every closed invariant set meets both W and X∖W. Simplicity fails: a closed invariant subset gives a proper
  ideal I, and EL_2(R,I) is a proper normal subgroup. The simplicity step uses minimality only through the fullness of e_V.
- *The Fibonacci subshift.* The hypotheses hold, so EL_2(R_Fib) is a simple Kazhdan LEF group inside G_Fib = EL_3(R_Fib).

## 4. Relation to the note
The main-tip note (d10dd73cad) says at l.53 "The same holds for $\EL_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$ for every
$n\ge3$." Theorem B extends this to n = 2. The proposal artifact `sk-el2-proposal-2026-09-13.md` gives the verbatim
change and a compact rank-two paragraph.
