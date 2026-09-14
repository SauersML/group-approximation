# sk-review-2, part 4: queue entries 17-18 (2026-09-13)

- **Verifier:** sk-referee-2.
- **Queue:** `sk/queue/sk-referee-2.txt`, entries 17-18.
- **Main's tip when read:** 4108325812.
- **Verdict key:** as in part 1.

## Summary
| # | id | owner | verdict |
|---|---|---|---|
| 17 | route `unit-idempotent-three-generators-goursat-proof` → `unit-idempotent-elementary-group-has-three-torsion-generators` | sk-generators | PASS |
| 17b | `sk-generators-proposal-2026-09-13.md`: P1 (drop 1 from the generating set), P2 (remark), P3 (Fibonacci example) | sk-generators | PASS for all three; P1 carries one integration note |
| 18 | `topological-full-group-embeds-in-subshift-elementary-group` (+ `-proof`) | sk-subgroups | PASS |
| 18b | `sk-subgroups-proposal-2026-09-13.md`, Options 1/2 | sk-subgroups | PASS |

## 17. Three torsion generators via Goursat
**Checks.**
- **c has order 7.** c = [[0,0,1],[1,0,1],[0,1,0]] has det(xI+c) = x(x²+1)+1 = x³+x+1. This polynomial is irreducible over F_2, so c has order 7.
- **t and w are involutions.** t = I+N with N = (1+p)E_12 + pE_13 and N² = 0, so t² = I, and t ≠ I. w = [[0,u,0],[u^{−1},0,0],[0,0,1]] and w² = I.
- **The finite subgroup.** For p ∉ {0,1}, F_2[p] = F_2p ⊕ F_2(1+p) ≅ F_2×F_2, so EL_3(F_2[p]) = SL_3(F_2)². Under this identification t ↦ (e_12(1), e_13(1)).
  - ct_0 = [[0,0,1],[1,1,1],[0,1,0]] has characteristic polynomial x³+x²+x+1 = (x+1)³. Row 1 of (ct_0+I)² is (1,1,0) ≠ 0, so ct_0 has order 4.
  - ct_1 = [[0,0,1],[1,0,0],[0,1,0]] is a 3-cycle, of order 3.
  - So both projections have order divisible by 28 or 42. The maximal subgroups of GL_3(F_2) have orders 24, 24 and 21, so both projections are onto.
  - Goursat's lemma: the subgroup is either SL_3(F_2)² or the graph of an automorphism. In the graph case the element (ct_0, ct_1) would have equal orders, but they are 4 and 3. So the subgroup is SL_3(F_2)², and ct has order 12.
- **The unit.** s = e_12(1)e_21(1)e_12(1) lies in SL_3(F_2) ⊆ ⟨c,t⟩, and ws = diag(u,u^{−1},1). Conjugation gives e_13(u^{±1}), and constant permutation matrices move a root to any position.
- **The coefficient ring.** The coefficient set is a subring containing 1, p and u^{±1}, so it is R. Also c, t, w ∈ EL_3(R), so Γ = EL_3(R).
- **The Fibonacci model.** u ↦ P_5 and p ↦ diag(1,0,1,1,0) generate M_5(F_2) (primitive return word), so the same three matrices generate SL_15(F_2).

PASS.

**17b. The proposal.**
- **P1: drop 1 from the generating set (l.94-95).** e_ij(1) = ∏_a e_ij(e_a), and l.185-187 recover 1 as Σ_C e_C. TRUE.
  - Integration note: EJZ's explicit set Σ includes x_0 = 1 (sk-expanders-limits Option C, reviewed in part 2). If Option C is used, its constant refers to the set containing e_ij(1).
  - With 1 dropped, the note's generating set is ⊆ Σ. The Kazhdan constant only improves for a larger set, so a bound for the smaller set needs a remark. This is not an issue while Option C stays in Cairn.
- **P2: the remark.** Its mathematics is the route above. TRUE. I agree with the owner's verdict against adding it to the note.
- **P3: the Fibonacci example.** The cyclic windows of abaab are aba, baa, aab, aba, bab, which give the set {aab, aba, baa, bab} = L_3(X_Fib). The letter a sits at positions 0, 2, 3, so D(e_a) = diag(1,0,1,1,0) and the model lies in GL_15(F_2). TRUE.
  - It agrees with sk-open-3's first model (B_1 → SL_15) and b965d63ba's remark.

## 18. The topological full group inside G_X
**Lemma 1.**
- u^n e_A u^m e_B = u^{n+m} e_{T^{−m}A ∩ B}.
- On {n_h = m} ∩ T^{−m}{n_g = n}, gh = T^{n+m}. So w_g w_h = w_{gh}, a homomorphism for the composition gh = g∘h. As a check, w_T = u.
- (ii) Both sides of w_g e_V = e_{gV} w_g equal Σ_n e_{g(A_n∩V)} u^n.
- (iii) The u^0 coefficient of w_g is e_{A_0}.

TRUE.

**Lemma 2.**
- Over F_2: e_12(a)e_21(a^{−1}) = [[0,a],[a^{−1},1]], then ·e_12(a) = [[0,a],[a^{−1},0]], and w(a)w(1) = diag(a,a^{−1}).
- In the product diag(a,a^{−1},1)·diag(b,b^{−1},1)·diag((ba)^{−1},ba,1), the slots are aba^{−1}b^{−1}, a^{−1}b^{−1}ba = 1, and 1.

TRUE.

**Corollary A.** The images of commutators are products of Whitehead matrices, so [[T]]' → G_X is an injective homomorphism. TRUE.

**Index by flux.**
- (gh)^ = ĝ∘ĥ, and ind(ĥ^{−1}ĝ^{−1}N, N) = I(g) + I(h) by bijection invariance.
- I(T) = |{−1}| = 1.
- Elements of finite order have index 0.

TRUE.

**Lemma 3.**
- w_g = (1−e) + Σ_a E_{π(a),a}, where E_{π(a),a} = u^{π(a)−a} e_{T^aW}.
- Φ is a homomorphism GL_{3h_0}(F_2) → GL_3(R). It sends transvections into G (note l.205-215), and GL = SL over F_2.
- diag(w_g,1,1) = Φ(diag(P_π,I,I)).

TRUE.

**Lemma 4 (generation), the delicate step.**
- **Step 1.**
  - |A| − |B| = I(g_1) = 0. ĝ_1(A) ⊆ [0,M) and ĝ_1(B) ⊆ [−M,0).
  - The levels T^jV (|j| ≤ 2M) are pairwise disjoint. So returns of y to V have |n'| > 4M, and orbit points in the tower with n' ≠ 0 have |m| > 3M and move by < 2M without crossing 0.
  - For n ≥ 0 with n ∉ B, ĝ_1(n) ≥ 0 lies outside ĝ_1(A) ∪ ĝ_1(B), so σ̂ keeps it ≥ 0. Points of ĝ_1(B) are sent into ĝ_1(A) ⊆ [0,M).
  - So ĥ(N) ⊆ N, ĥ(Z∖N) ⊆ Z∖N, and ĥ is a bijection of N. TRUE.
- **Step 2.**
  - Returns to Y are > 2M', and n_h is constant on T^jY for |j| ≤ M'. Refining the Kakutani–Rokhlin bases makes n_h constant on levels.
  - Middle levels stay in their tower because |n_h| ≤ M'.
  - The bottom levels use c_j and h(T^jy) ∈ O^+(y), which gives 0 ≤ j+c_j ≤ 2M' < r.
  - The top levels use x ∈ T^{−i}Y with i = r−j, and h(T^{−i}y) ∈ O^−(y), which gives r−2M' ≤ j+c_{−i} < r.
  - So h permutes the levels of finitely many refined towers, and it is a product of Lemma 3 elements. TRUE.
- **Step 3.** g = T^k σ̃^{−1} h.

**Theorem B.**
- φ = diag(w_g, u^{−I(g)}, 1) is multiplicative slot by slot and injective.
- φ(T) is a Whitehead matrix, and level permutations have index 0 and map into Φ(GL). So the image lies in G. TRUE.

**Cross-check with entry 13** (`binary-subshift-ring-k1-is-half-orbit-index`, PASS in part 3).
- ind(w_g) = −I(g) and ind(u^{−I(g)}) = I(g), so φ(g) has index 0, as membership in EL_3 requires.
- On [[T]]' the index vanishes, which agrees with Corollary A. The two independent lanes agree.

PASS.

**18b. The proposal (Options 1/2).**
- The paragraph's sentences are correct: w_g is a unit and g ↦ w_g is an injective homomorphism; Whitehead gives diag(a,a^{−1},1); the displayed product is right.
- Matui Theorems 4.9 and 5.4 are stated for D([[φ]]_0) = D([[φ]]), per the remark after Theorem 4.8, as quoted in `derived-full-group-fg-iff-minimal-subshift-citation`. Juschenko–Monod Theorem A is quoted in `minimal-cantor-full-groups-are-amenable-citation`.
- The owner's forward-reference caveat is right: Option 2, at the end of §1, avoids the forward reference.
- The reader-merit call belongs to main and the user. It is a striking structural fact, but no stronger headline.

PASS.
