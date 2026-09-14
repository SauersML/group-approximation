# sk-verify-19: independent verification, part 3 (2026-09-14)

Lane sk-verify-19, serving `sk2/queue/verify.txt` from the bottom. This part covers queue lines 11, 10, 9 and 8. Every step was re-derived by hand. None of these claims had a review line on main before this.

## 1. Line 11: `laurent-linear-confining-sets-force-infinite-order-elements` (Theorem L, sk-cstar-genericity). PASS

**Statement.** Let Γ ⊇ Λ = SL_3(F_2[u^{±1}]), and let H ≤ Γ be confined by a finite P ⊆ Λ∖{1}. Then H contains a conjugate of an infinite-order element of Λ.

**Re-derived.**
- **Λ ≤ G_X.** A = F_2[u^{±1}] is Euclidean (it is a localization of F_2[u]), so SL_3(A) = E_3(A) (recalled, standard). And A ⊂ LC(X,F_2)⋊Z, because distinct powers of u are linearly independent.
- **Step 2 (Φ_p ≢ 0).**
  - The only scalar in SL_3(F_2(u)) is 1, since F_2(u) contains no primitive cube root of unity (F_2 is algebraically closed in F_2(u)).
  - So p ≠ 1 has a v with pv ∉ F_2(u)v. With h = (v, λw, pv) and det h = 1: h e_1 = v and h e_3 = pv.
  - Hence p′e_1 = h^{-1}pv = e_3 and q′e_3 = h^{-1}p^{-1}pv = e_1, so p′_{31} = q′_{13} = 1 and Φ_p(h) = 1.
- **Step 3 (generic h ∈ Λ).**
  - Z = ⋃_{p∈P}{Φ_p = 0} is a proper closed subset of the irreducible SL_3.
  - Each root group e_ij(F_2[u]) is infinite, hence Zariski-dense in U_ij. So the Zariski closure of Λ contains every U_ij, and so equals SL_3.
  - So some h ∈ Λ∖Z exists, and k = hdh^{-1} ∈ Λ.
- **Step 4 (trace).**
  - [p,k^m] = h[p′,d^m]h^{-1}, and tr[p′,d^m] = Σ_{i,l}p′_{il}q′_{li}u^{m(d_l−d_i)} (commutative coefficients in A).
  - The δ-classes occupy degrees [δm−2D, δm+2D]. They are pairwise disjoint for |m| > 4D.
  - The δ = 2 class is the single term Φ_p(h)u^{2m} ≠ 0, whose degree range misses the constants. So the trace is non-constant.
- **Step 5 (finite order ⇒ constant trace).** Eigenvalues of a finite-order element are roots of unity, so the trace is algebraic over F_2 and lies in F_2(u), hence in F_2.
- **Step 6 (pigeonhole).** With g_i = k^{N_i} and gaps > 4D, Lemma R (§3) gives an H-element conjugate to [p, k^{N_i−N_j}], which has infinite order.
- **Corollary L′.** EL_3(F_2) ⊆ Λ, so no nontrivial torsion subgroup of G_X is confined by a subset of Λ∖{1}. That covers the constant units of Lemma B.

**Model tests.** [e_12(1), d^m] = e_12(1)·e_12(u^m) = e_12(1+u^m) has order 2, so the generic twist h is necessary. For p = diag(u,u^{-1},1), [p,d^m] = 1, while Φ_p(h) ≠ 0 generically. Both consistent.

## 2. Line 10: `polynomially-small-units-have-order-dividing-420` (Lemma X). PASS-WITH-FIXES

**Re-derived.**
- 1 = c_1σ + c_{−1}σ^{−1} + c_2σ² + c_{−2}σ^{−2}, multiplied by σ², shows σ is a root of Q(t) = c_2t⁴ + c_1t³ + t² + c_{−1}t + c_{−2}. Its t² coefficient is 1, so Q ≠ 0, and A = F_2[σ] has dimension ≤ 4.
- A is a finite commutative algebra, a product of local A_i with residue fields F_{2^{f_i}}, f_i ≤ 4. So |F^×| ∈ {1,3,7,15}.
- 𝔪_i^4 = 0, so (1+x)^4 = 1 + x^4 = 1. The exponent of A_i^× divides 4·|F_{2^{f_i}}^×|, and the exponent of A^× divides 4·lcm(3,7,15) = 420.

**Fix (W1, 0 lines).** Say why σ ∈ A^× and not merely in M^×: σ is invertible in M, so it is not a zero divisor in A, and a non-zero-divisor of a finite ring is a unit. The proof uses σ ∈ A^× without saying so.

**Consequence checked.** A subgroup K ⊆ B_4 ∪ {1} has all element orders dividing 420, hence exponent dividing 420.

## 3. Line 9: `confined-subgroup-pigeonhole-commutator-lemma` (Lemma R, R′, R″). PASS

**Re-derived.**
- Confinement at g_i gives p_i ∈ P ∩ g_iHg_i^{-1}, so h_i = g_i^{-1}p_ig_i ∈ H. By pigeonhole, p_i = p_j = p for some i ≠ j.
- With k = g_ig_j^{-1}: g_j = k^{-1}g_i and h_j^{-1} = g_i^{-1}kp^{-1}k^{-1}g_i. So h_ih_j^{-1} = g_i^{-1}[p,k]g_i ∈ H.
- **R′.** Take n = r+1; the H-element is conjugate to an infinite-order commutator.
- **R″.** If H had exponent dividing e, the H-element g_i^{-1}[p,k]g_i would satisfy x^e = 1, contradicting [p,k]^e ≠ 1. ("Nontrivial" is not needed.)

## 4. Line 8: `frobenius-support-idempotents-give-boolean-realization` (sk-normalizer-recognition: Lemma S, Lemma D, Proposition F). PASS

**Lemma S re-derived.**
- (a) |K| = 21 is odd, so P_V² = 21P_V = P_V and kP_V = P_Vk = P_V.
  - P_V fixes Fix(K) pointwise (21m = m) and maps into it.
  - P_V − I = Σ_k(k−I) (21 ≡ 1), so (I−P_V)M ⊆ [M,K]; and P_V(k−I) = 0 gives [M,K] ⊆ ker P_V.
- (b) Σ_{q∈F21}q = 0 on F_2³, since F21 has no nonzero fixed vector (Singer cycle). So S_V = e_VI_3.
- (c) S_∅ = 0; for V ≠ ∅, some k ≠ I and M is faithful, so S_V ≠ 0.
- (d) Disjoint supports commute.
- (e) Immediate.

**Lemma D re-derived.**
- A_0 = α(E3_U) commutes with K = α(F21_{X∖U}), by the import C2 (rigid supports are mutual centralizers, PASS). So A_0 preserves S_{X∖U}M and Fix(K).
- S_U and S_{X∖U} commute, which gives four joint pieces M_{ab}. K′ = α(F21_U) is trivial on M_{0b} and fixed-point-free on M_{1b}, because Fix(K′) ∩ [M,K′] = 0.
- (⇒) M_{11} ⊆ Fix(K′) ∩ [M,K′] = 0, and faithfulness gives S_US_{X∖U} = 0.
- (⇐) S_{X∖U}M = M_{01} ⊆ Fix(K′). The kernel of A_0 on it is normal and contains K′ ≠ 1, and E3_U is simple, so the kernel is A_0.

**Proposition F re-derived.**
1. **The Boolean homomorphism.**
   - For disjoint V and W, (O) kills the joint piece S_VS_WM. On the remaining pieces the diagonal α(F21_{V⊔W}) acts as K_V (fixed-point-free), as K_W, or trivially.
   - So Fix(α(F21_{V⊔W})) = (I−S_V)(I−S_W)M, and [M, α(F21_{V⊔W})] is the sum of the other two pieces (each piece is its own commutator space when there are no fixed vectors).
   - So S_{V⊔W} = S_V + S_W.
   - (O′) gives complements. Meets follow by expanding over three disjoint pairs. Injectivity is Lemma S(c).
2. **α(E3_V) lies in I + S_VM_3(R_Y)S_V.** By Lemma D with (O) for (V, X∖V) and (O′), α(E3_V) is trivial on (I−S_V)M and preserves S_VM. So g − I = S_V(g−I)S_V.
3. **α(L_X) commutes with every S_V.** L_X = L_V × L_{X∖V}, with each factor inside the corresponding E3. So α(L_V) commutes with S_V, and α(L_{X∖V}) commutes with I − S_V.

**Model tests.** α = id and α = inn(diag(u,1,1)) (S_V = diag(e_{TV}, e_V, e_V), non-scalar, with (O) and (O′) holding) are consistent. So is the fake natural ⊕ trivial, which fails (O′).

**Imports and conditions.**
- The corner isomorphism e_U(LC(X,F_2)⋊Z)e_U ≅ LC(U,F_2)⋊_{T_U}Z (first-return reduction) is standard but, as the lane flags, not source-checked. Lemma D (⇐) depends on it through simplicity of E3_U.
- The statement is conditional on the hypotheses (O) and (O′), and says so.
