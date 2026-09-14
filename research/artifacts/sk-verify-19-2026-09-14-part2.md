# sk-verify-19: independent verification, part 2 (2026-09-14)

Lane sk-verify-19, serving `sk2/queue/verify.txt` from the bottom. This part covers queue lines 7, 6, 5 and 4. Every step was re-derived by hand; the imports were checked against their main nodes. Main tip at review: 19a6841d98. None of these claims had a review line on main before this.

## 1. Line 7: `cyclic-factor-subshift-groups-have-ring-type-shadows` (Corollary S, sk-rank3-shadows). PASS-WITH-FIXES

**Re-derived.**
- **Cyclic partition.** m ∈ Cyc(X) gives a continuous f: X → Z/m with f∘T = f+1. For U = f^{-1}(0) we get T^iU = {y : f(T^{-i}y) = 0} = f^{-1}(i), so X = ⊔_{i<m}T^iU and T^mU = U.
- **The induced system.** The first return time to U is exactly m, so (U, T^m|_U) is the first-return map, hence minimal. Coding by m-blocks makes it a subshift. It is infinite.
- **Rank rewriting.** Import [T] (PASS sk-verify-3/5) gives R_X ≅ M_m(R_{X_1}) with matrix units u^ie_Uu^{-j}, and EL_3(M_m(S)) = EL_{3m}(S), since transvections inside a block are commutators through another block. So G_X = EL_{3m}(R_{X_1}), with 3m ≥ 6.
- **Change of marking.** If (Q_k,T_k) → (G,T) and T′ is another finite generating set, writing T′ in T and T in T′ gives markings T′_k that eventually generate Q_k, with (Q_k,T′_k) → (G,T′). So [D] (PASS sk-verify-14 part7, N = 3m ≥ 4) applies to the elementary marking of EL_{3m}(R_{X_1}): eventually Q_k ≅ PSL_{3md_k}(F_{q_k}), induced by surjective ring maps ρ_k.
  - d_k → ∞ because G_X is infinite simple.
  - Characteristic 2 comes from 2 = 0 in R_{X_1}, so eventually 2 ∈ ker ρ_k.
- **Divisibility.** [E] (PASS sk-verify-14 part7): Div(EL_{3m}(R_{X_1})) ⊇ {3m·c : c ∈ Cyc(X_1)}, so for each fixed c the natural dimension 3md_k is divisible by 3m·c for all large k.

**Fixes (0 lines).**
- **F1:** the node's third bullet should read "for each c ∈ Cyc(X_1), the natural dimension is eventually divisible by 3m·c". The "all large k" depends on c.
- **F2:** the artifact's "Cyc(X) = m·Cyc(X_1) as supernatural data" is not used by the statement. Only c ∈ Cyc(X_1) ⇒ mc ∈ Cyc(X) holds as written. Drop it or say "contains".

## 2. Line 6: `subshift-group-isomorphism-preserves-rational-spectrum` (Theorem R, sk-rank3-shadows). PASS

**Statement.** For n ≥ 3, EL_n(R_X) ≅ EL_n(R_Y) implies Cyc(X) = Cyc(Y).

**Re-derived.** By symmetry it suffices to take m ∈ Cyc(Y) with m ≥ 2.
1. **Rank nm.** As in §1, EL_n(R_Y) = EL_{nm}(R_{Y_1}), with nm ≥ 6.
2. **nm ∈ Div(EL_n(R_Y)).** This is [E] with N = nm and c = 1 ∈ Cyc(Y_1).
3. **Transport.** Div is an isomorphism invariant ([E]: changing the marking preserves converging sequences, and the natural dimension of PSL_M(F_q) is well defined for large M). So nm ∈ Div(EL_n(R_X)).
4. **Contradiction if m ∉ Cyc(X).**
   - [C1] (PASS-WITH-FIXES sk-verify-14 part2; fix F1 there does not touch C1/C2): g_r | g_{r+1}, and m ∈ Cyc iff m | g_r for large r. If m ∉ Cyc(X), then m ∤ g_r for every r, since divisibility at one level propagates upward.
   - [C2]: for large N ≡ 0 mod g_r there is a primitive periodic word of length N with the (r+1)-language of X. Primitivity (least period N) makes the ring models onto M_N(F_2), so the approximants are SL_{nN}(F_2) = PSL_{nN}(F_2).
   - Take N_k = g_{r_k}p_k, with r_k → ∞ slowly and primes p_k > m large enough for [C2]. Then (SL_{nN_k}(F_2), elementary marking) → EL_n(R_X).
   - If nm | nN_k, then m | g_{r_k}p_k, and gcd(m,p_k) = 1 gives m | g_{r_k}, a contradiction.
   - So nm ∉ Div(EL_n(R_X)), contradicting step 3.

**Model tests.** Thue–Morse (Cyc ∋ 2^j) against Sturmian (Cyc = {1}) gives non-isomorphic groups. Two Sturmian slopes give no conclusion. X = Y is trivially consistent.

**Scope.**
- "Rational spectrum is a strong orbit equivalence invariant" is recalled and not used in the theorem. The theorem is correct as stated.
- Imports used: [T], [C1], [C2], [D], [E], all PASS on main.

## 3. Line 5: `stable-finite-actions-extension-sofic-iff-class-norm-vanishes` (Theorem 2, sk-deligne-sofic). PASS-WITH-FIXES

**⇐ direction** is Theorem 1 (§4 below).

**⇒ direction re-derived.**
- Let τ_n on V_n be a sofic approximation of Γ~, and Q its limit A-free measured Γ~-algebra.
- **The quotient approximation of Γ.** A acts almost freely, so V_n/A carries almost-actions of Γ.
  - Words trivial in Γ lift into A and act trivially on A-orbits.
  - For g ≠ 1, every lift g~a (a ∈ A, finitely many) is ≠ 1 in Γ~, so it moves most points, and g moves most A-orbits.
  - So V_n/A is a sofic approximation of Γ with limit algebra P = Q^A.
- **Import item 2** (Gohla–Thom Theorem 3.4, citation node from the primary PDF): θ_*^P(α) = 0.
- **Stability** (Gohla–Thom Definition 3.7): P is weakly contained in the finite Γ-actions.
- **Import item 1** (Lemma 2.13 and the proof of Corollary 2.14): if P is weakly contained in a family 𝒫, then |||θ^P(α)||| ≥ inf_{Q∈𝒫}|||θ^Q(α)|||. With 𝒫 the finite actions, inf_X |||θ^X(α)||| = 0. The direction matches the import exactly.
- **On a finite action X** with the presentation complex as 2-skeleton and uniform cell weights, the least Hamming measure of a representative α + δb is the defect fraction of b. So |||θ^X(α)||| = ν_X(α) there, and inf_X ν_X(α) = 0.

**Fixes (0–1 line).**
- **F1 (import scope):** step 4 of the route and the artifact appeal to "Gohla–Thom §2.2" for model and weight comparability. That section is not in the import node `gohla-thom-class-norm-drops-under-weak-containment`. Either add §2.2 to the citation import, or state that the norm is computed on the presentation-complex model with uniform cell weights, where equality with ν_X holds by definition. Whether the infimum is 0 needs only bounded distortion.
- **F2 (one line):** add the justification above that V_n/A is a sofic approximation of Γ with limit P = Q^A. The route asserts it without the reason.

With F1–F2 the theorem is correct. It is Gohla–Thom's mechanism read as an equivalence, as the lane credits.

## 4. Line 4: `finite-actions-with-vanishing-class-norm-make-extension-sofic` (Theorem 1, sk-deligne-sofic). PASS

**Re-derived.**
1. **Amplification.**
   - V_n = X_n × Γ/N_n with the diagonal action; pull b_n back along the projection. Defective cells over (x,gN_n) are exactly those over (x,r), so the fraction is unchanged ((M3)).
   - For g ∉ N_n, normality gives g·hN_n = hN_n iff g ∈ N_n. So g moves every point of Γ/N_n, hence of V_n, once n is large enough for g.
2. **Permutations.**
   - τ(s)(v,t) = (s·v, t + b(s,s·v)) is a bijection of V_n × A. τ(a) translates.
   - The relations of A and [a,s] hold exactly, since A is abelian and translations commute with τ(s).
   - For r ∈ R the base action is exact (r = 1 in Γ), so τ(r)(v,t) = (v, t + hol_r(v)), and r = a_r at (v,t) iff the cell (v,r) is not defective.
3. **Trivial words.**
   - w = w′a with w′ ∈ F(S), trivial in Γ.
   - A van Kampen diagram of radius C_w maps into the action complex at each base point. Because A is abelian, hol_{w′}(v) is the signed sum of the cell holonomies (discrete Stokes).
   - If no cell within radius C_w of v is defective, the sum equals the value of w′ on the lifts, which is −a, so τ(w) fixes (v,t).
   - Each defective cell affects at most |B_{C_w}| base points, so the bad fraction is ≤ |B_{C_w}||R|ν_n → 0.
4. **Nontrivial elements.**
   - If g ≠ 1, τ(w) covers g, which moves every point for large n.
   - If g = 1 and g~ = a ≠ 0, outside the bad fraction τ(w)(v,t) = (v,t+a) ≠ (v,t).
5. **Conclusion.** τ_n is a sofic approximation of Γ~.

**Model tests.**
- A split extension has b = 0, with no defects.
- For a residually finite Γ~, a finite quotient injective on A gives ν = 0.
- For a non-residually-finite Γ~, ν_X > 0 for every X, so only the infimum can vanish.
- All consistent.

**Credit.** The amplification is Alekseev–Thom arXiv:2512.15494 Lemma 3.2, as the lane records. The torsor construction is elementary.

**Consequence for the Deligne route.** `deligne-triple-cover-sofic-from-vanishing-finite-norms` rests on Theorem 1 plus the open `deligne-class-finite-action-norms-vanish`. It is correct as an implication. The CSP reduction to congruence covers is correctly marked a remark with an unread import (Mennicke; Bass–Milnor–Serre).
