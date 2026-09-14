# sk-free-6 part 3: bounded elementary generation of G_X (2026-09-13)

Lane sk-free-6. This closes Open D of parts 1–2 positively.
- Part 1: `research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md`
- Part 2: `research/artifacts/sk-free-6-normal-generation-2026-09-13-part2.md`

## 0. Statement
**Theorem D.** Let (X,T) be a minimal homeomorphism of an infinite Cantor set, R = LC(X,F_2) ⋊_T Z and G = EL_3(R). Every h ∈ G is a product of at most 78 elementary matrices e_ij(r), r ∈ R. The sequence of positions (i,j) can be fixed in advance, so G = e_{i_1j_1}(R) ⋯ e_{i_78j_78}(R).

**Corollary E.**
1. G is bounded in the sense of Burago–Ivanov–Polterovich: every conjugation-invariant norm on G is bounded.
2. For every g ≠ e, cw(g) < ∞: some N_g has every element of G a product of N_g conjugates of g^{±1}. For a nonempty clopen V,

   1/inf_μ μ(V) ≤ cw(e_12(χ_V)) ≤ 312·(⌊1/inf_μ μ(V)⌋ + 1).

   So G is boundedly simple but not uniformly simple, and the invariant measures of X measure exactly how uniform simplicity fails.
3. Every element of G is a product of at most 78 involutions, and G is a product of 78 locally finite elementary abelian 2-subgroups (root subgroups).

## 1. Tools
Notation.
- In the faithful orbit representation (part 1, F6), each a ∈ M_3(R) acts on F_2[Z]^3 at a point x by a banded matrix a_x(m,n) ∈ M_3(F_2).
- The entry a_x(m,n) vanishes for |m−n| > deg a and depends locally constantly on T^m x.
- For h ∈ GL_3(R), put w := max(deg h, deg h^{-1}).
- For a half-line J = (−∞,c) or [c,∞), P_J is the coordinate projection and V_J = F_2[J]^3 (finitely supported vectors).

**(T1) Finite block Gauss reduction.** Let S = ∏_a M_{h_a}(F_2) be a finite product with all h_a ≥ 3. Every A ∈ GL_3(S) is a product of at most 39 elementary matrices over S, in a fixed pattern.

*Proof.*
- **Stable rank.** S is semisimple Artinian, so sr(S) = 1. The first column (a_1,a_2,a_3) of A is left unimodular.
- **Column 1.** sr ≤ 2 gives t with (a_1 + t a_3, a_2) unimodular; sr = 1 gives t′ with p := a_1 + t a_3 + t′a_2 a unit. So e_12(t′)e_13(t) makes the pivot p. Two more left elementary matrices clear rows 2 and 3.
- **Row 1.** Two right elementary matrices clear it, leaving diag(p, A′) with A′ ∈ GL_2(S).
- **A′.** One left operation makes its pivot a unit, one clears below, and one right operation clears the row. So A = (6 left)·diag(p,q,r)·(3 right) up to inverses: 9 elementary matrices.
- **Diagonal.** diag(p,q,r) = diag(p,p^{-1},1)·diag(1,pq,(pq)^{-1})·diag(1,1,pqr).
  - Each diag(c,c^{-1},1) is 6 elementary matrices in characteristic 2: e_12(c)e_21(c^{-1})e_12(c) = [[0,c],[c^{-1},0]], times e_12(1)e_21(1)e_12(1) = [[0,1],[1,0]].
  - v := pqr ∈ GL_1(S) = ∏_a SL_{h_a}(F_2). By Thompson (R. C. Thompson, Trans. Amer. Math. Soc. 101 (1961) 16–33; the only exceptions are n = 2 with |K| ≤ 3), each component of v is a commutator [x_a, y_a] in SL_{h_a}(F_2). Choosing componentwise gives v = [x,y] with x, y ∈ GL_1(S).
  - diag([x,y],1,1) = diag(x,x^{-1},1)diag(y,y^{-1},1)diag((yx)^{-1},yx,1) is 18 elementary matrices, and the same holds for diag(1,1,[x,y]) in positions (3,·).
- Total: 9 + 12 + 18 = 39. ∎

**(T2) Index.** For h ∈ GL_3(R), a point x and a cut c, the compression Q = P_J h_x P_J on V_J is Fredholm, and ind Q = dim ker Q − dim coker Q equals 0 whenever h ∈ G.

*Proof.*
- **Fredholm.** Qξ = 0 means h_xξ is supported within w outside J, so ξ = h_x^{-1}(h_xξ) is supported within 2w of c. Every vector supported deeper than 2w inside J lies in Im Q (take ξ = h_x^{-1}η). So ker and coker are finite.
- **Additivity.** P(ab)P − (PaP)(PbP) = Pa(1−P)bP has finite rank, and the index is additive and invariant under finite-rank perturbations (linear algebra over a field).
- **Root elements.** For a = e_ij(r) = I + N with N² = 0, Q² = I + PNPNP = I − PN(1−P)NP is the identity up to finite rank, so 2 ind Q = 0. ∎
- Since ind(P_{(−∞,c)} h P_{(−∞,c)}) + ind(P_{[c,∞)} h P_{[c,∞)}) = ind h_x = 0 up to finite rank, both half-lines have index 0.

**(T3) End correction with banded inverse.** Let h ∈ G and J = (−∞,c), with Q as above and W = 2w.
- There is a linear map F on V_J, supported in the window L_c = [c−W, c) (rows and columns), such that Q + F is bijective.
- (Q+F)^{-1} = P_J h_x^{-1} P_J + D with D supported in [c−4W, c)².
- F can be chosen depending only on the entries of h_x in the window [c−3W, c+W), hence the same for equal local configurations. The same holds for J = [c,∞).

*Proof.*
- **Choice of F.** K := ker Q ⊆ L_c. Choose a complement L′ of K in L_c. Since V_J = Im Q + L_c, choose M ⊆ L_c with V_J = Im Q ⊕ M, so dim M = dim coker Q = dim K by (T2).
  - Set F = 0 on L′ and on the far coordinates, and let F map K isomorphically onto M.
  - Then Q + F is bijective. These choices depend only on the local window.
- **Localized inverse.** Put B′ = P_J h_x^{-1} P_J.
  - (Q+F)B′ = P − P h(1−P)h^{-1}P + FB′ = P + E, with E supported in [c−2W, c)².
  - Likewise B′(Q+F) = P + E″ with E″ supported in [c−2W, c)².
  - D := (Q+F)^{-1} − B′ satisfies D = −(Q+F)^{-1}E (columns in the window) and D = −E″(Q+F)^{-1} (rows in the window). ∎

**(T4) Two ends.** Let B = [c_0, c_1) with c_1 − c_0 ≥ 16W. Put A_B := P_B h_x P_B + F_top + F_bot, with F_top from (T3) for (−∞,c_1) and F_bot for [c_0,∞). Then A_B is invertible on V_B, with inverse Ã := P_B h_x^{-1} P_B + D_top + D_bot.

*Proof.* Take a column δ_n with n in the upper half of B.
- Ãδ_n = (Q_top+F_top)^{-1}δ_n, because D_bot δ_n = 0 and P_B h^{-1}δ_n = P_{(−∞,c_1)}h^{-1}δ_n.
- ξ := Ãδ_n is supported within 4W of n or of c_1, so it is far from c_0. So P_B hξ = Q_topξ and F_botξ = 0, giving A_Bξ = δ_n.
- The lower half is symmetric. So A_BÃ = P_B, and A_B is a square finite matrix. ∎

## 2. Proof of Theorem D
Let h ∈ G, w as above, W = 2w.
1. **Towers.** Take L ≥ 32W and a Kakutani–Rokhlin partition 𝒫 with bases B_a and heights h_a ≥ L (part 1, F5). Refine the base atoms so that each atom determines h's entries in the window of radius L + 4W around its tower, including the adjacent towers. Finitely many atoms suffice, since return times are bounded by minimality.
   - A_𝒫 ⊆ R is the subalgebra spanned by u^{i−i′}χ_{T^{i′}B_a} for levels 0 ≤ i,i′ < h_a in the same tower a.
   - A_𝒫 ≅ ∏_a M_{h_a}(F_2), and M_3(A_𝒫) consists of the elements acting block-diagonally on tower occurrences, with entries depending only on (a, levels).
2. **First factor.** Let H_1 act on each tower occurrence B by the corrected compression A_B of (T4). The corrections are chosen per local type, so H_1 ∈ M_3(A_𝒫).
   - Its inverse (T4) also lies there, so H_1 ∈ GL_3(A_𝒫).
   - By (T1) (h_a ≥ L ≥ 3), H_1 is a product of at most 39 elementary matrices, each over A_𝒫 ⊆ R.
3. **Localization.** Z := H_1^{-1}h − I acts as 0 on δ_n with n farther than 6W from every cut:
   - h_xδ_n stays inside the occurrence and far from its ends, and Ã agrees with h_x^{-1} there.
   - For n near a cut, (H_1^{-1}h)δ_n is supported within 6W of that cut.
   - So Z is supported in ⋃_c [c−6W, c+6W)², with no interaction between different cuts.
4. **Second factor.** Let 𝒫′ be the Kakutani–Rokhlin partition over the midpoint levels ⋃_a T^{⌊h_a/2⌋}B_a, refined in the same way. Its occurrences contain exactly one cut neighbourhood each, at distance ≥ L/4 from their ends.
   - I + Z and its inverse h^{-1}H_1 = I + Z′ (localized likewise) lie in M_3(A_𝒫′). So H_2 := I + Z ∈ GL_3(A_𝒫′).
   - By (T1), H_2 is a product of at most 39 elementary matrices.
5. **Count.** h = H_1H_2 is a product of at most 78 elementary matrices. The pattern of (T1) is fixed, so the positions (i_k, j_k) are fixed. ∎

**Where the index is used.** Step 2 needs dim ker = dim coker at each end (T2).
- **u ⊕ u ⊕ 1** (index −2) has nothing to match at the top, as it must fail: diag(u,u,1) ∉ G.
- **diag(u,u^{-1},1).** At the top the u-component loses δ_{c_1−1} and the u^{-1}-component misses δ_{c_1−1}, so F_top turns component 1 into component 2; F_bot turns it back. So A_B is a permutation matrix of a cycle through both components, and its inverse is banded.
- The wrap-around of part 2 §2.2 came from choosing cyclic shifts *within* each component. End-local corrections avoid it.

## 3. Proof of Corollary E
1. **Boundedness.** A conjugation-invariant norm ‖·‖ satisfies ‖h‖ ≤ 78·max ‖e_ij(r)‖. Each e_ij(r) = [e_ik(r), e_kj(1)] is a product of 2 conjugates of e_kj(1)^{±1}, which is a permutation conjugate of e_12(1). So ‖h‖ ≤ 156‖e_12(1)‖.
2. **Conjugacy width.** Part 1, Corollary C gives that e_12(1) is a product of at most M′ conjugates of g^{±1}, with M′ finite. With g = e_12(χ_V), Theorem B with U = X gives M′ ≤ 2⌊ρ_max⌋ − ⌈ρ_min⌉ + 3 ≤ 2⌊1/inf_μ μ(V)⌋ + 2. So cw(g) ≤ 78·2·(2⌊1/inf_μ μ(V)⌋ + 2) = 312(⌊1/inf_μ μ(V)⌋ + 1). The lower bound is Theorem A.
3. **Involutions.** e_ij(r)² = e_ij(2r) = I, and root subgroups are elementary abelian 2-groups; they are locally finite because R is an F_2-vector space. ∎

## 4. Remarks, model tests, credit
- **Why this is not automatic.** R has no known stable rank one (`minimal-cantor-crossed-product-has-stable-rank-at-most-two` is open for 1) and contains F_2[u^{±1}] (stable rank 2).
  - The proof never uses sr(R). It cuts the orbit into long towers, where the finite algebras have stable rank one.
  - The Fredholm index at a cut, which vanishes on G, is the only obstruction to cutting.
- **Two-sided picture.** Theorem D with Theorems A–B: G_X is boundedly generated by root subgroups and bounded in the Burago–Ivanov–Polterovich sense, yet its normal generation widths are not uniform, and the obstruction is exactly the simplex of invariant measures.
- **Other ranks and fields.** The same proof gives a bound C(n) for EL_n(R), n ≥ 3. Over F_q with q > 2, the determinant and the centre need care (GL_h(F_q) ≠ SL_h(F_q)); not claimed here.
- **Model test (odometer, part 2 §2.1).** Theorem D gives a uniform bound there too. It uses entries in R, which contains M_{2^n}(F_2[t^{±1}])-blocks. This does not contradict the stable rank 2 obstruction for block Gauss reduction over M_k(F_2[t^{±1}]): the proof cuts along towers, not along matrix blocks.
- **Credit.**
  - Thompson 1961 (commutators in SL_n).
  - Kakutani–Rokhlin towers (Herman–Putnam–Skau 1992).
  - Bounded elementary generation for arithmetic rings: Carter–Keller(–Paige); a 2023 preprint arXiv:2307.05526 treats Steinberg groups over Dedekind rings of arithmetic type and over F_q[t,t^{-1}] (abstract only, from a web search).
  - Strang's factorization of banded matrices with banded inverses (recalled) is the nearest linear-algebra analogue.
- **Search bound.** A web search for bounded elementary generation of EL_n over algebraic crossed products of Cantor minimal systems found no match; neither did a grep of main for "bounded generation" with subshift nodes. Novelty is unconfirmed beyond that.
