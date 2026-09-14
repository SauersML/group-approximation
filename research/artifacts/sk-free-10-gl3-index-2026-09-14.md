# sk-free-10: GL_3 over the binary subshift ring is G_X ⋊ Z, its normal subgroups, and outer automorphisms of G_X (2026-09-14)

Lane sk-free-10 (wave 12, free lane). Every result below is proved completely here and is unreviewed; each is queued with the verifier.

**Setting.** (X,T) is an infinite minimal Cantor system and R = LC(X,F_2) ⋊_T Z, with u f u^{-1} = f∘T^{-1}. G = G_X = EL_3(R) and d = diag(u,1,1).

## 0. Inputs
- **(I1)** `crossed-product-gl-n-has-infinite-cyclic-index-quotient` (PASS, sk-verify-5).
  - For x ∈ X let V_x = ⊕_{t∈Z} F_2^3 δ_t with f δ_t = f(T^t x) δ_t and u δ_t = δ_{t+1}. This is faithful and banded.
  - For a cut c put P = P_{[c,∞)}. For g ∈ GL_3(R) the compression P g P on P V_x is Fredholm, and ind_{x,c}(g) = dim ker − dim coker is a homomorphism GL_3(R) → Z.
  - ind vanishes on every e_ij(r), and ind(d) = −1.
- **(I2)** `subshift-el-groups-boundedly-elementary-generated` (Theorem D; PASS-WITH-FIXES twice, sk-verify-15 and sk-verify-16, band 7W and L ≥ max(32W,3)). Its proof is in `research/artifacts/sk-free-6-normal-generation-2026-09-13-part3.md` §1–§2.
- **(I3)** The simplicity proof of Theorem 2 in the paper (rev4.3 §1), reviewed by sk-rev4-referee-a and sk-perfect-a.

## 1. The index does not depend on the point or the cut
**Lemma 1.** For g ∈ GL_3(R), ind_{x,c}(g) is independent of x ∈ X and c ∈ Z. Write ind(g).

*Proof.* Let w bound the band of g and g^{-1}.
- **Cut.** P_{[c+1,∞)} V_x has codimension 3 in P_{[c,∞)} V_x. Compressing a Fredholm operator to a subspace of finite codimension does not change its index: the difference from Q' ⊕ id on the complement has finite rank, and the index is invariant under finite-rank perturbation and additive on direct sums. So ind_{x,c} = ind_{x,c+1}.
- **Translation.** The basis change δ_t ↦ δ_{t−1} identifies V_{Tx} with V_x and carries the cut c to c+1. So ind_{Tx,c} = ind_{x,c+1} = ind_{x,c}.
- **Local constancy.** Put Q = P g_x P and Q' = P g_x^{-1} P.
  - QQ' = P − E and Q'Q = P − E', with E = P g_x (1−P) g_x^{-1} P and E' likewise. Both are supported in [c, c+2w)².
  - So ker Q and a complement of Im Q lie in the window [c, c+2w), and ind(Q) is a finite linear-algebra quantity of the entries of g_x and g_x^{-1} on [c−2w, c+4w).
  - Those entries depend only on T^t x for t in a bounded window, through finitely many clopen sets. So x ↦ ind_{x,c}(g) is locally constant.
- **Conclusion.** A locally constant T-invariant integer function on a minimal X is constant: its level sets are clopen, T-invariant and nonempty. ∎

For invertible g_x on V_x, the two half-line compressions differ from g_x by the finite-rank off-diagonal corners. So
  ind(P_{(−∞,c)} g_x P_{(−∞,c)}) = −ind(P_{[c,∞)} g_x P_{[c,∞)}) = −ind(g).
Check: for g = d, the right compression is the unilateral shift (index −1), and the left one has kernel δ_{c−1} and is onto (index +1).

## 2. Theorem O1: the index kernel is the elementary group
**Theorem O1.** ker(ind: GL_3(R) → Z) = EL_3(R) = G_X. Every h ∈ GL_3(R) with ind(h) = 0 is a product of at most 78 elementary matrices, in the fixed pattern of (I2). Consequently:
- **(a)** GL_3(R) = G_X ⋊ ⟨d⟩, d has infinite order, and GL_3(R)/G_X ≅ Z via ind.
- **(b)** G_X = [GL_3(R), GL_3(R)].
- **(c)** GL_3(R)/EL_3(R) → K_1(R) is injective, since ind factors through K_1 by (I1) stability. It is an isomorphism if K_1(R) ≅ Z (`binary-subshift-ring-k1-is-half-orbit-index`, unreviewed). No stable-rank input is used.

*Proof.* (I1) gives EL_3(R) ⊆ ker(ind).

Conversely, let h ∈ GL_3(R) with ind(h) = 0, and let w bound the band of h and h^{-1}, W = 2w.
- **(T2) for h.** By Lemma 1 and the display after it, both half-line compressions at every point x and every cut c have index 0: dim ker Q = dim coker Q.
- **Where Theorem D uses membership in G.** Reading the proof of (I2) line by line, the hypothesis h ∈ G enters only through (T2), at one place: the choice dim M = dim K in the end correction (T3). All other steps use only h ∈ GL_3(R) and the band w of h and h^{-1}:
  - (T3) the localized inverse (Q+F)^{-1} = P h_x^{-1} P + D;
  - (T4) the two-end inverse on a block of length ≥ 16W;
  - Step 1, Kakutani–Rokhlin towers of height ≥ L ≥ max(32W,3), with base atoms refined so that each atom determines h along its tower occurrence plus margins;
  - Step 2, the first factor H_1 ∈ GL_3(A_𝒫) of corrected compressions;
  - Step 3, localization of Z = H_1^{-1}h − I near the cuts, band 7W;
  - Step 4, the second factor H_2 = I + Z ∈ GL_3(A_𝒫′);
  - (T1), block Gauss reduction for ANY invertible element of M_3(∏_a M_{h_a}(F_2)). This needs sr = 1 of the finite semisimple algebra, GL_1 = ∏ SL_{h_a}(F_2) over F_2, and Thompson's commutator theorem, and none of these refers to G.
- **Conclusion.** With (T2) established for h, the proof of (I2) runs verbatim and gives h = H_1 H_2, each a product of ≤ 39 elementary matrices over subalgebras A_𝒫, A_𝒫′ ⊆ R. So h ∈ EL_3(R).

**(a)** For k ∈ GL_3(R), ind(k d^{ind(k)}) = ind(k) − ind(k) = 0, so k d^{ind(k)} ∈ G. ⟨d⟩ ∩ G = 1, because ind(d^m) = −m. G is normal as a kernel.

**(b)** [GL_3, GL_3] ⊆ ker(ind) = G, since Z is abelian. G is simple and nonabelian, so G = [G,G] ⊆ [GL_3, GL_3].

**(c)** ind is additive and stable under diag(M,1) (I1), so it induces K_1(R) → Z, and GL_3(R)/EL_3(R) → K_1(R) → Z is ind, injective by the theorem. ∎

**Model tests.**
- diag(u,u,1) has index −2, so it is not in G. Theorem D's remark "u⊕u⊕1 has nothing to match at the top" is exactly the failure of (T2).
- diag(u,u^{-1},1) has index 0, and indeed lies in G by Whitehead's identity.
- uI_3 has index −3, so it is not in G, although conjugation by it is the ring automorphism α_T.
- **Scope.** Minimality and infiniteness are used in Lemma 1 (constancy of the index) and in (I2) (towers). For a periodic orbit of size p, u^p I_3 is central with index −3p, and O1's conclusion G = [GL_3, GL_3] would need the center; the statement does not claim that case.

## 3. Theorem O2: normal subgroups of GL_3(R)
**Theorem O2.** Let K ≤ GL_3(R) be normalized by G. Then K = 1 or K ⊇ G. So the normal subgroups of GL_3(R) are exactly 1 and ind^{-1}(mZ) = G⟨d^m⟩ for m ≥ 0.

*Proof.* Let 1 ≠ g ∈ K. We follow the simplicity proof of Theorem 2 in the paper (I3), noting where g ∈ GL_3(R), not g ∈ G, is enough.
1. **Small sets.** Let w bound the lengths of the u-exponents in the entries of g and g^{-1}. Call a clopen V small if V ∩ T^t V = ∅ for 0 < |t| ≤ 2w and every f∘T^a (|a| ≤ w, f a coefficient of an entry of g^{±1}) is constant on V. Every nonempty clopen set contains a small one, since T has no periodic points.
2. **A noncommuting root.** If g commuted with every e_ij(e_V), V small, the entrywise computation of (I3) would give g = cI_3 with c ∈ LC(X,F_2) invertible, so c = 1 and g = 1. That computation uses only the entries of g, never g ∈ G. Fix h = e_ij(e_V) not commuting with g.
3. **The commutator lies in K and in a finite simple tower group.**
   - k := [g,h] = g·(h g^{-1} h^{-1}) ∈ K, because g ∈ K and K is normalized by h ∈ G; and k ≠ 1.
   - As in (I3), with ε_ab = e_{T^aV} u^{a−b} (|a|,|b| ≤ w), the entries of g e_V E_ij g^{-1} lie in the span A_V ≅ M_{2w+1}(F_2) of the ε_ab. So k − I and k^{-1} − I lie in M_3(A_V), and k ∈ H_V ≅ GL_d(F_2), d = 3(2w+1) ≥ 3.
   - H_V ≤ G. K ∩ H_V is normalized by H_V and contains k ≠ 1, so H_V ⊆ K by simplicity of GL_d(F_2) = PSL_d(F_2). Hence e_pq(e_V) ∈ K for all p ≠ q.
4. **Level ideal.** J = {r ∈ R : e_pq(r) ∈ K for all p ≠ q} is a two-sided ideal:
   - J is additive, since K is a group;
   - for l ∉ {p,q}, e_pq(sr) = [e_pl(s), e_lq(r)] ∈ K when r ∈ J and s ∈ R: conjugating e_lq(r) ∈ K by e_pl(s) ∈ G stays in K;
   - symmetrically e_pq(rs) = [e_pl(r), e_lq(s)] ∈ K.
   - J contains e_V, so it contains every e_{T^t V} = u^t e_V u^{-t}. By minimality and compactness finitely many translates cover X, so 1 = 1 − ∏_i (1 − e_{T^{t_i}V}) ∈ J. So J = R and K ⊇ EL_3(R) = G.
5. **Classification.** If K is normal and nontrivial, then K ⊇ G, and K/G is a subgroup of GL_3(R)/G ≅ Z (O1a). So K = ind^{-1}(mZ) for a unique m ≥ 0. Conversely each ind^{-1}(mZ) is normal, as the preimage of a subgroup of an abelian quotient. ∎

Remark: the center of GL_3(R) is Z(R)^× I_3 = F_2^× I_3 = 1 (Lemma 2 below), so there is no central alternative. The unreviewed node `amenable-crossed-product-gl-normal-structure-is-standard` asserts the sandwich for every amenable Γ and field through Stepanov. O2 does not use it: it gives the full list over F_2 for Z, through the paper's reviewed proof and O1.

## 4. Theorem O3: outer automorphisms of G_X
**Lemma 2.** The centralizer of G in GL_3(R) is trivial, and Z(R) = F_2.

*Proof.*
- **Center of R.** Take r = Σ_n c_n u^n central. From r f = f r for all f ∈ LC(X,F_2): c_n (f∘T^{-n} − f) = 0, so for n ≠ 0, c_n vanishes on every clopen set where some f separates x from T^n x. Aperiodicity gives c_n = 0. From ru = ur, c_0∘T^{-1} = c_0, so c_0 is constant by minimality.
- **Centralizer.** If k commutes with every e_ij(1), the entrywise criterion (k_pi = 0 for p ≠ i, and k_ii = k_jj) gives k = cI_3. Commuting with e_ij(r) for all r gives c ∈ Z(R)^× = {1}. ∎

**Theorem O3.**
- **(a)** Conjugation gives an injective homomorphism GL_3(R) → Aut(G), and inn(k) is inner in G iff k ∈ G. So GL_3(R)/G ≅ Z embeds in Out(G_X), and [inn(d)] has infinite order in Out(G_X).
- **(b)** For φ ∈ Aut(X,T), the automorphism group of the subshift (homeomorphisms commuting with T), α_φ(Σ f_n u^n) = Σ (f_n∘φ^{-1}) u^n is a ring automorphism of R fixing u, hence an automorphism of G. The homomorphism
  Φ: Z × Aut(X,T) → Out(G_X), (m, φ) ↦ [inn(d^m) ∘ α_φ]
  has kernel {(−3n, T^n) : n ∈ Z}. So (Z × Aut(X,T))/⟨(−3,T)⟩ ↪ Out(G_X). In particular Aut(X,T) ↪ Out(G_X), and Out(G_X) has an element of infinite order even when Aut(X,T) = ⟨T⟩.

*Proof.*
- **(a)** k ↦ inn(k)|_G has kernel C_{GL_3}(G) = 1 (Lemma 2). If inn(k) = inn(g) on G with g ∈ G, then g^{-1}k centralizes G, so k = g. With O1a this gives the embedding and the infinite order.
- **(b), homomorphism.**
  - α_φ is a ring automorphism: α_φ(u f u^{-1}) = f∘T^{-1}∘φ^{-1} = f∘φ^{-1}∘T^{-1} = u α_φ(f) u^{-1}, since φT = Tφ. Also α_{φψ} = α_φ α_ψ.
  - α_φ(d) = d, so α_φ ∘ inn(d) ∘ α_φ^{-1} = inn(α_φ(d)) = inn(d). The two commute, and (m,φ) ↦ inn(d^m) α_φ is a homomorphism into Aut(G).
- **(b), kernel.** Suppose inn(d^m) α_φ = inn(g) with g ∈ G. Then α_φ = inn(k) on G with k = d^{-m} g ∈ GL_3(R).
  - α_φ fixes e_ij(1) and e_ij(u), so k commutes with all of them. As in Lemma 2, k = cI_3 with c ∈ R^×, and cu = uc.
  - The centralizer of u in R is {Σ c_n u^n : c_n∘T = c_n} = F_2[u^{±1}], by minimality. c^{-1} also commutes with u, so c is a unit of F_2[u^{±1}], namely u^n.
  - Then α_φ(f) = u^n f u^{-n} = f∘T^{-n} for all f, so φ = T^n.
  - Additivity of ind with ind(u^n I_3) = −3n (three diagonal copies of the unilateral shift, (I1)) and ind(d^{-m} g) = m gives m = −3n.
- **(b), converse.** inn(d^{-3n}) α_{T^n} = inn(d^{-3n} u^n I_3), and d^{-3n} u^n I_3 has index 3n − 3n = 0, so it lies in G by O1 and the automorphism is inner. ∎

**Model tests.**
- **Sturmian X.** Aut(X,T) = ⟨T⟩ (recalled: Olli, ETDS 2013; not source-checked, and not used in any claim). Then the image of Φ is (Z × Z)/⟨(−3,1)⟩ ≅ Z, generated by [inn(d)]. Since α_T = inn(uI_3) and uI_3·d^{-3} has index 0, [α_T] = [inn(d)]^3.
- **Contrast with lattices.** Out(SL_3(Z)) is finite. Here Out(G_X) contains Z. G_X has property (T) (EJZ) and is simple, so infinite Out is not excluded by (T): Paulin's finiteness theorem is for hyperbolic groups.

## 5. Scope, credit, novelty
- **Firewall.** O3 gives lower bounds only. That these automorphisms, with flips (X,T) ≅ (X,T^{-1}) and transpose-inverse with the adjoint anti-automorphism, generate Out(G_X) needs standardness of isomorphisms. That is owned by sk-normalizer-recognition (`subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer`), so not claimed.
- **Other ranks.** The Theorem D remark gives a bound C(n) for EL_n, n ≥ 3; the same argument would give ker(ind|_{GL_n}) = EL_n(R). Not claimed here.
- **Credit.**
  - The index is the half-orbit Fredholm index (I1), classical in form (Pimsner–Voiculescu, Putnam for C(X)⋊Z).
  - The cutting argument is sk-free-6's Theorem D.
  - Putnam's topological stable rank one gives the C*-analogue, that the unitary group of C(X)⋊Z has K_1 = Z at every size; O1 is an algebraic, unstable, rank-three counterpart without stable rank.
  - Vaserstein's stability theorems would give O1c from sr(R) ≤ 2, which is open (`minimal-cantor-crossed-product-has-stable-rank-at-most-two`).
- **Novelty check (bounded).** A grep of main found only (I1), which gives ⊆, sk-free-2's conditional C2, and sk-open-4's stable Theorem I. No web search was made.
