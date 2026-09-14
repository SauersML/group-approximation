# sk-verify-18 part 6: GL_3 over the subshift ring (2026-09-14)

Queue lines 12–14, sk-free-10, `research/artifacts/sk-free-10-gl3-index-2026-09-14.md`. None carried a sk-verify-19 review line at review time.
- `subshift-gl3-index-kernel-is-elementary-group` (Theorem O1, with Lemma 1);
- `subshift-gl3-normal-subgroups-are-index-preimages` (Theorem O2);
- `subshift-el3-out-contains-index-and-subshift-automorphisms` (Theorem O3, with Lemma 2).

## Verdicts
All three PASS, re-derived by hand. O1 is conditional on its reviewed inputs:
- (I1) `crossed-product-gl-n-has-infinite-cyclic-index-quotient` (sk-verify-5 PASS);
- (I2) Theorem D, `subshift-el-groups-boundedly-elementary-generated` (sk-verify-15 and sk-verify-16 PASS-WITH-FIXES: band 7W, L ≥ max(32W,3)).

No FAIL, no GAP.

## Lemma 1: the index does not depend on the point or the cut
- **Cut.** P_{[c+1,∞)}V_x has codimension 3 in P_{[c,∞)}V_x. In block form Q = [[Q′,B],[C,D]] with B, C, D of finite rank, so Q − (Q′ ⊕ id) has finite rank. The algebraic Fredholm index is invariant under finite-rank perturbation and additive on direct sums, so ind Q = ind Q′.
- **Translation.** f(T^t·Tx) = f(T^{t+1}x), so δ′_t := δ_{t+1} identifies V_{Tx} with V_x and moves the cut by one. Hence ind_{Tx,c} = ind_{x,c+1} = ind_{x,c}.
- **Local constancy.**
  - With Q = PgP and Q′ = Pg⁻¹P, QQ′ = P − E and Q′Q = P − E′, where E = Pg(1−P)g⁻¹P. Since g and g⁻¹ are w-banded, E and E′ are supported in [c, c+w)² ⊆ [c, c+2w)².
  - So ker Q ⊆ Im E′, and Im Q contains every vector supported away from the window. The index is a finite linear-algebra function of the entries of g_x and g_x⁻¹ in a bounded window, which depend on finitely many clopen conditions on the T^t x.
  - A locally constant, T-invariant integer function on a minimal X is constant.
- **Two half-lines.** g_x differs from P_−gP_− ⊕ P_+gP_+ by finite-rank corners, so the left index is −ind(g). This is the last line of Theorem D's (T2).

## Theorem O1
**Where Theorem D uses h ∈ G.** Checked line by line in `research/artifacts/sk-free-6-normal-generation-2026-09-13-part3.md` §§1–2.
- (T1) block Gauss reduction is for any A ∈ GL_3(∏_a M_{h_a}(F_2)); over F_2, GL_1 = ∏ SL_{h_a}, and Thompson's commutator theorem applies.
- (T2) is the only place membership enters: "ind Q = 0 whenever h ∈ G", through root elements plus additivity.
- (T3) uses it once, at "dim M = dim coker Q = dim K by (T2)", to let F map K onto M.
- (T4) and Steps 1–5 use only h ∈ GL_3(R) and the band w of h and h⁻¹: towers, H_1 ∈ GL_3(A_𝒫) through (T4) and (T1), localization of Z = H_1⁻¹h − I, and H_2 = I + Z ∈ GL_3(A_𝒫′).

**Conclusion.** If ind(h) = 0, Lemma 1 gives index 0 for both half-line compressions at every point and every cut. The proof then runs verbatim, and h = H_1H_2 with H_1 ∈ EL_3(A_𝒫) and H_2 ∈ EL_3(A_𝒫′), so h ∈ EL_3(R).

**Consequences.**
- **(a)** ind(k·d^{ind(k)}) = ind k − ind k = 0, so k·d^{ind(k)} ∈ G. And ⟨d⟩ ∩ G = 1, since ind(d^m) = −m.
- **(b)** [GL_3, GL_3] ⊆ ker ind = G, and G = [G,G] because G is simple and nonabelian.
- **(c)** ind is stable under diag(·,1), so it factors through K_1(R) → Z. A class in GL_3/EL_3 that maps to 0 in K_1 has index 0, so it lies in EL_3. The map is injective.

**Model tests re-checked.** diag(u,u,1) has index −2 and diag(u,u⁻¹,1) has index 0 (it lies in G by Whitehead), matching (T3)'s example. uI_3 has index −3. The periodic case is excluded, as stated.

## Theorem O2
- **Normal root.** Take 1 ≠ g ∈ K, where K ≤ GL_3(R) is normalized by G. The note's small sets, the commuting criterion for e_ij(r), and "g commutes with every e_ij(e_V) ⇒ g = cI with c ∈ LC(X,F_2)^× = 1" use only the entries of g and g⁻¹.
- **Commutator.** k = [g,h] = g·(hg⁻¹h⁻¹) lies in K, since h ∈ G normalizes K. The product formula f u^a e_V f′u^b ∈ {0, ε_{a,b⁻¹}} uses only entries, so k ∈ H_V ≅ GL_d(F_2) with H_V ≤ G. Then K ∩ H_V ⊴ H_V is nontrivial, and simplicity of GL_d(F_2) (d ≥ 3) gives H_V ⊆ K.
- **Level ideal.** For r ∈ J, e_pq(sr) = (e_pl(s)e_lq(r)e_pl(s)⁻¹)·e_lq(r)⁻¹ ∈ K, and symmetrically for rs. J contains the translates of e_V, and a finite cover gives 1 ∈ J, so K ⊇ G.
- **Classification.** A nontrivial normal K contains G, and K/G ≤ GL_3/G ≅ Z by O1(a), so K = ind⁻¹(mZ). Conversely each preimage is normal. The center is trivial (Lemma 2), so no central alternative occurs.

## Theorem O3 and Lemma 2
- **Center of R.** For r = Σc_n u^n, rf = fr for all f gives c_n(f∘T⁻ⁿ − f) = 0. Aperiodicity separates each x from Tⁿx, so c_n = 0 for n ≠ 0. ru = ur gives c_0∘T⁻¹ = c_0, so c_0 is constant.
- **Centralizer of G.** k commutes with every e_ij(1), so by the entrywise criterion k = cI; commuting with every e_ij(r) forces c ∈ Z(R)^× = {1}.
- **(a)** GL_3(R) → Aut(G) has kernel C(G) = 1, and inn(k) is inner in G iff k ∈ G. So GL_3/G ≅ Z embeds in Out(G_X).
- **(b), homomorphism.** For φ ∈ Aut(X,T), α_φ is a ring automorphism: φT = Tφ gives α_φ(ufu⁻¹) = u·α_φ(f)·u⁻¹. It fixes u and d, commutes with inn(d), and α_{φψ} = α_φα_ψ. So (m,φ) ↦ [inn(d^m)α_φ] is a homomorphism.
- **(b), kernel.**
  - Suppose inn(d^m)α_φ = inn(g) with g ∈ G. Then α_φ = inn(k) on G with k = d⁻ᵐg.
  - α_φ fixes e_ij(1) and e_ij(u), so k = cI with cu = uc.
  - C_R(u) = {Σc_n uⁿ : c_n∘T = c_n} = F_2[u^{±1}] by minimality, and its units are the uⁿ. Then f∘φ⁻¹ = f∘T⁻ⁿ for all f, so φ = Tⁿ.
  - ind(uⁿI_3) = −3n and ind(d⁻ᵐg) = m, so m = −3n.
  - Conversely α_{Tⁿ} = inn(uⁿI_3) on R, and d⁻³ⁿuⁿI_3 has index 0, so it lies in G.
  - So the kernel is {(−3n, Tⁿ)}, Aut(X,T) embeds, and [α_T] = [inn(d)]³, because (0,T) − (3,id) = (−3,T) lies in the kernel.

## Notes (0 lines)
- The recalled Olli result (Aut of Sturmian subshifts) and the Paulin remark are not used in any claim, as the artifact says.
- O1(c)'s "isomorphism if K_1(R) ≅ Z" rests on the unreviewed `binary-subshift-ring-k1-is-half-orbit-index`, and is stated conditionally there.
