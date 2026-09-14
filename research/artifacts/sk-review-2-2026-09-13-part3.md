# sk-review-2, part 3: queue entries 8-16 (2026-09-13)

- **Verifier:** sk-referee-2.
- **Queue:** `sk/queue/sk-referee-2.txt`, entries 8-16.
- **Main's tip when read:** 18375ec10e.
- **Verdict key:** as in part 1.
- **Prior parts:** 2506d7ea48 (part 1), 3bf9734c16 (part 2).

## Summary
| # | id | owner | verdict |
|---|---|---|---|
| 8 | `fibonacci-words-model-balls-of-fibonacci-kazhdan-group` (+ `fibonacci-words-model-balls-proof`) | sk-open-3 | PASS |
| 9 | `brown-mcduff-witness-for-simple-kazhdan-lef-group` (+ `-proof`) | sk-operator-algebras | PASS; Kirchberg p. 552 read independently |
| 9b | repairs to `simple-kazhdan-group-gives-property-t-factor-in-r-omega` (+ `-proof`) and `kirchberg-property-t-fp-implies-rf-citation` | sk-operator-algebras | PASS. Part 1 items 1b, 1c and 2.i are resolved |
| 9c | Option B LaTeX for l.150-152 (`sk-operator-algebras-proposal-2026-09-13.md` §3) | sk-operator-algebras | PASS+repair |
| 10 | `rational-eigenvalue-iff-subshift-ring-is-matrix-ring` (+ `-proof`) | sk-open-4 | PASS; the artifact needs one fix |
| 11 | `measure-rank-functions-are-limits-of-periodic-word-models` (+ `-proof`) | sk-open-4 | PASS |
| 12 | `minimal-cantor-crossed-product-k-theory-formula` (+ `-proof`) | sk-open-4 | PASS |
| 13 | `binary-subshift-ring-k1-is-half-orbit-index` (+ `-proof`) | sk-open-4 | PASS |
| 14 | `binary-cantor-ring-stable-steinberg-group-centrally-closed` (+ `-proof`) | sk-open-4 | PASS |
| 15 | `subshift-elementary-group-lef-growth-complexity-bounds` (+ `-proof`) | sk-lef-growth | PASS |
| 16 | `sturmian-elementary-group-lef-growth-is-exp-r-squared` (+ `-proof`), and the `refuted_by` edit | sk-lef-growth | PASS |

Still open from part 1, not yet applied by sk-questions-oa, on `simple-kazhdan-group-lacks-factorization-property`:
- (1.i) the title's clause "strictly beyond residual amenability" needs its one-line proof, or should be dropped;
- (1.ii) credit Ozawa's p. 26 remark.

## 8. Fibonacci models of balls
**Checks.**
- **Item 1.**
  - Counting letters shows f_k is primitive, so z^∞ has least period N.
  - A bi-infinite sequence with p(L) ≤ L has a period at most L (Morse–Hedlund). For L < N this gives p(L) ≥ L+1.
  - f_{k+3} = f_{k+1}f_kf_kf_{k−1} contains zz, so every word of z^∞ of length ≤ N+1 lies in zz, hence in L(X).
  - |L_L(X)| = L+1 forces equality for L ≤ N−1. TRUE.
- **Item 2.**
  - f_{k+4} = f_{k+1}f_kf_kf_{k−1}f_kf_{k−1}f_k contains zz f_{k−1}f_{k−1}f_{k−2}.
  - f_{k−1}f_{k−2} and f_{k−2}f_{k−1} differ exactly in their last two letters.
  - So the prefix of z^∞ of length 3N+|f_{k−1}|−2 occurs in X. The windows starting in [0,N) have length up to 2N+|f_{k−1}|−1 = |f_{k+2}|−1. TRUE.
- **Item 3.**
  - Entries of B_r have windows in [−r,r] and exponents ≤ r, and entries of B_rB_r have windows in [−2r,2r].
  - D_z is defined on A_{2r} through points of X, which exist since 4r+1 ≤ 2N−3 ≤ |f_{k+2}|−1.
  - P^iD_z(g)P^{−i} = D_z(g∘T^{−i}), because both sides evaluate g on (z^∞)_{n−i+W}.
  - Injectivity: N ≥ 2r+1 gives disjoint cyclic diagonals, and L_{2r+1}(X) occurs in z^∞ by item 1. TRUE.
- **Item 4.** 4r+1 ≤ N+1. TRUE.
- **Numbers.** B_1 → SL_15 (N=5 ≥ 4); B_2, B_3 → SL_24 (N=8); B_4, B_5 → SL_39 (N=13).
- **N < φ(2r+2).** If F_j < M ≤ F_{j+1}, Binet gives F_{j+1} < φF_j + 1 ≤ φ(M−1) + 1 < φM. TRUE.
- **Kazhdan constant with d = 3.** e_b = 1−e_a. 12√6+6+36√2 = 86.306…, so 8× that is 690.45… and κ > 1/691. The gap bound 1/(48·691²) = 4.36…·10^(−8). TRUE.
- **Computed thresholds.** Labeled "not proved"; not re-run.

## 9. Brown's McDuff witness
**(a) PASS.** This is the construction recommended in part 1 §2 (2.i):
- L(S) is a factor because S is ICC;
- L(S) ↪ R^ω (Ozawa Prop. 7.1);
- M = L(S) ⊗̄ R is separable and McDuff;
- M ↪ R^ω through R^ω ⊗̄ R → (R⊗̄R)^ω.

**(b) PASS, source read independently.** Springer PDF, doi:10.1007/BF01459798, p. 552, fetched on MSI and read as a page image. Verbatim:
- "Theorem 1.1 A discrete group with property (F) and property T is residually finite."
- "Corollary 1.2 For a discrete group G with property T, the following properties are equivalent: (i) G has property (F). (ii) There exists a faithful unitary representation from G into the hyperfinite II_1-factor. (iii) … (iv) G is residually finite. (v) …"
- "The implications (iv) ⇒ (v) ⇒ (iii) ⇒ (i) and (iv) ⇒ (ii) ⇒ (i) are true in full generality."

A faithful S → U(R) would give (F) by (ii)⇒(i), then residual finiteness by Theorem 1.1. That is impossible for an infinite simple group.

**9b.** The repaired citation now quotes (iv)⇒(ii)⇒(i), which gives the converse direction. So `kirchberg-property-t-fp-implies-rf` is correctly stated as an "iff", and part 1 item 1b is resolved. Issue 1 and pages 551-563 are correct (1c resolved). The Brown paragraph of the R^ω-factor node now points to the separable witness (2.i resolved).

**9c. Option B LaTeX** (l.150-152 plus a Kirchberg bibitem).
- Every sentence is true and the citations match the sources above.
- **Repair (9c.i).** "So $G$ does not have the factorization property" skips the reason the reader needs, namely that G is not residually finite. Write: "Since $G$ is infinite and simple, it is not residually finite, so it does not have the factorization property, and ...". This costs +0 to +1 line.
- **Integration note.** Option B keeps the old "permutation matrices give hyperlinear models" sentence. sk-referee-2 P3 and Option A of sk-expanders-limits replace that sentence with the pinned citation [Example 4.5 and Theorem 3.3]. Option B's new sentences can follow either version.

## 10. Rational eigenvalue ⟺ matrix ring
**Checks.**
- **(1)⇒(2).** |f| and f^p are invariant, hence constant, so U = f^{−1}(ζ) and T^aU = f^{−1}(ζλ^a). The levels are disjoint and cover X, and T^pU = U. TRUE.
- **(2)⇒(5).**
  - E_abE_cd = χ_{T^aU ∩ T^{a−b+c}U}u^{a−b+c−d} = δ_bc E_ad, since 0 < |c−b| < p and the levels are disjoint. Also ΣE_aa = 1.
  - The corner χ_U R χ_U = LC(U)⋊_{T^p}Z, because χ_U u^j χ_U = 0 unless p | j.
  - (U, T^p) is minimal by the saturation argument. TRUE.
- **(5)⇒(4).** Z(R_X) = F_q ≅ Z(S) ⊆ S, so M_p(F_q) ⊆ M_p(S). TRUE.
- **(5)⇒(3).** [1] = p[e_11] in K_0. `subshift-crossed-product-k0-is-coinvariant-group` sends [1] to [χ_X] (PASS at group level by sk-verify-3). TRUE.
- **(3)⇒(1).** χ_X = ph + g − g∘T^{−1} gives ḡ(Tx) − ḡ(x) = 1 in Z/p, so f = λ^{ḡ} is an eigenfunction. TRUE.
- **Groups.**
  - EL_n(M_p(S)) = EL_{np}(S) for n ≥ 2, through products of commuting elementary matrices and commutators through a second block.
  - R_{Z/p} ≅ M_p(F_q[u^{±p}]) ↪ R_X.
  - F_q[t^{±1}] is Euclidean, so E_m = SL_m. TRUE.
- **Factor maps.** h ↦ h∘π is injective, unital and equivariant, so it extends to the crossed products. TRUE.

**Artifact repair (10.i).** `sk-open-4-dictionary-2026-09-13-part2.md` §1 says "EL_n(R_X) ≅ EL_{np}(R_{(U,T^p)}) for every n ≥ 1". That is false at n = 1, where EL_1 is trivial. The node correctly says n ≥ 2, so change the artifact to n ≥ 2.

## 11. Measure rank functions from the periodic models
**Checks.**
- **(a)** Zeroing couplings between blocks of length L changes the rank by ≤ 2wm(N/L+1).
  - A block's rank is a function of the widened word of y_k, which lies in L(X) once L+2(ρ+w) ≤ 2k+1.
  - Averaging over the L offsets gives Σ_v ν_k[v] rank_v / L + O(wm/L) + O(L/N_k). ν_k → μ on cylinders, and the finite-L expressions are Cauchy within O(wm/L), so the limit exists, uniformly in μ. TRUE.
- **(b) Sylvester axioms.** They pass to limits because D_k is exactly multiplicative on any fixed finite configuration for large k, and rk_μ(χ_U) = μ(U).
  - Affine and continuous in μ: uniform limit of continuous affine expressions.
  - Ergodic case: Ara–Claramunt uniqueness, Prop `proposition-unique.rank`(ii) as quoted in `cantor-z-crossed-product-embeds-in-continuous-factor`, requires a full ergodic μ. Minimality gives full support.
  - General μ: the barycentric formula for continuous affine functions, then faithfulness from the ergodic components. TRUE.
- **(c)** Generic segments that start at a fixed 2k-word v and are followed by v, concatenated in proportion. The joins lie inside v, so no new (2k+1)-words appear, and the frequencies are within ε plus O(k/N). A diagonal weak* limit gives all μ. TRUE.
- **(d)** Rank is invariant under multiplication by units. rk(A+B) ≤ rk A + rk B gives subadditivity through gh−I = g(h−I) + (g−I). Faithful; rk_μ(χ_U E_12) = μ(U), with the unnormalized convention rk(I_3) = 3, consistent with dividing by N_k in (a). TRUE.

## 12. K_n formula for minimal Cantor crossed products
**Checks.**
- The imports quote verbatim: ABC Theorem 3.6 plus Lemma 7.2 for regular supercoherent A, giving a long exact sequence in all degrees; Quillen via Weibel IV Cor. 1.13; supercoherence of LC(X,F_q) re-derived in the K_0 route (PASS).
- K_n(A) = LC(X, K_n(F_q)) by filtered colimits.
- ker(1−σ_*) = M by minimality, and coker = K^0 ⊗ M by right exactness.
- Assembly:
  - n = 2i: 0 → 0 → K_{2i}(R) → Z/(q^i−1) → 0;
  - n = 2i+1: 0 → K^0 ⊗ Z/(q^{i+1}−1) → K_{2i+1}(R) → 0;
  - n = 1: a split extension by Z.
- Over F_2: K_1 = Z, K_2 = 0, K_3 = K^0/3. Model tests: Bass–Heller–Swan and Morita. PASS.

## 13. K_1 is the half-orbit index
**Checks.**
- π respects ufu^{−1} = f∘T^{−1}.
- The compression correction Pπ(M)(1−P)π(M^{−1})P has rank ≤ kw, so Pπ(M)P is invertible modulo finite rank. The algebraic index is additive and ignores finite-rank changes, so ind is a homomorphism.
- Elementary matrices compress to unipotents, so they have index 0. ind(u) = −1 from the unilateral shift.
- K_1(R_X) = Z (entry 12), so the surjection is bijective.
- **GPS index.**
  - π(a_γ)δ_n = δ_{σ(n)} with displacement ≤ w, so ind = −(flux across 0).
  - The flux is the same across every cut, and Birkhoff at a generic x gives ∫ n_γ dμ.
  - The index is independent of x, since it is a homomorphism on K_1.
  - Model test γ = T. TRUE.
- **Consequence.** diag(u,1,1) ∉ G_X. This agrees with ROSTER-B's correction that a ↦ diag(a,1,1) embeds only index-0 units, such as [[T]]'. PASS.

## 14. Stable Steinberg group over F_2
**Checks.**
- For any Cantor homeomorphism, K_2(A) = LC(X,K_2(F_2)) = 0 and K_1(A) = LC(X,F_2^×) = 0, so the exact segment K_2(A) → K_2(R) → K_1(A) forces K_2(R) = 0.
- St(R) ≅ E(R), H_2(E) = K_2 = 0 (Weibel III Thm 5.5), and H_3(E) = H_3(St) ≅ K_3 (Weibel IV, after Cor. 1.7.1, Gersten).
- For minimal (X,T), K_3 = K^0/3 (entry 12). PASS.

## 15. General LEF growth bounds (artifact parts 1-2)
**Checks.**
- **Lemma 0.** Induction on prefixes. TRUE.
- **Theorem A.**
  - The windows of ball products lie in [−2r,2r].
  - The cyclic (4r+1)-window model is well defined and multiplicative, invertible on g·g^{−1}, and injective because N ≥ p_X(4r+1) ≥ 4r+2 > 2r and the (2r+1)-words occur.
  - (c) q − p ≤ (R_X(n)−n+1) + (R_X(n−1)−n+1) ≤ 2R_X(n).
  - (d) A covering walk in the Rauzy graph gives N ≤ EV + V.
  - A1: E−V = 1, so the graph is a cycle plus one ear, and the walk around C, along P and back along C has length ≤ 2E = 2n+2. TRUE.
- **Lemma 1.** w_ik(s) = e_ik(s)e_ki(s^{−1})e_ik(s) has block [[0,s],[s^{−1},0]] over F_2. D = w_ik(u)w_ik(1) = diag(u, u^{−1}) at (i,k). D^{−1} is the reversed word. Conjugation multiplies the entry by u^{±1} on the left, and D′ does the same on the right. +12 letters per unit. TRUE.
- **Lemma 2.** T(h+1) ≤ 4T(h) + 48·2^h with T(0) = 1 gives T(h) ≤ 4^h + 48·4^{h−1}·2 = 25·4^h. TRUE.
- **Theorem B (B2).**
  - Relations (i) have length 5·25·4^h = 125·4^h, and relations (ii) have length 100·4^h.
  - e_ij(a) and e_kl(b) commute when ab = ba = 0.
  - Perfect, nontrivial, pairwise commuting subgroups: ker μ ⊆ ∏Z(P_v), and each P_v/Z(P_v) is nontrivial perfect, of order ≥ 60.
  - With h maximal, 2^h > √(r/500). TRUE.
- **Lemma 3.** The height filtration with involutive generators, including the reversed commutator case, gives |Ũ| ≤ 2^{d(d−1)/2}, and the kernel meets the centre. TRUE.
- **Lemma 4 and Theorem C.** ι is a non-unital injective ring homomorphism, so the τ_PQ satisfy the Lemma 3 relations.
  - |e_pq(E_ab(W))| ≤ κ+24m, so λ = 4(κ+24m) and the relations have length ≤ 5λ = 20κ+480m.
  - y_1d ≠ 1 by injectivity. TRUE.
- **(D2)** At r_i = 500n_i², log L ≥ log60·(r_i/500)^{2+ε/2}, which is not ≼ exp(r²). TRUE.
- **(D4)** Labeled a sketch.

PASS.

## 16. Sturmian LEF growth exp(Θ(r²))
**Checks.**
- **Reduction.** The letter swap maps S to S. For α < 1/2, q_1 = ⌊1/α⌋ = a.
- **Best approximation.** Proof by unimodular coordinates with η_n, η_{n+1} of opposite signs. TRUE.
- **ε < α.** |η_1| = 1 − q_1α, and 1 − aα < α iff α > 1/(a+1). TRUE.
- **W = {x_0 = 1, x_j = 1}, j = 1+s, sα ≡ −ε.**
  - + codings: [1−α,1) ∩ [1−2α+ε, 1−α+ε) = [1−α, 1−α+ε), with no wrap.
  - − codings: (1−α, 1−α+ε].
  - Codings are injective in θ, so a return with 0 < t ≤ 2m puts θ and θ−tα in one arc of length ε. So ‖tα‖ < ε, contradicting best approximation (2m < q_{n+1}). TRUE.
- **Cost.** 2·1 + 2(1 + 48|j|) ≤ 52 + 96m.
- **Theorem C threshold.** 20κ + 480m = 1040 + 2400m, and d(d−1)/2 = (6m+3)(3m+1) ≥ 18m².
- **Choice of m.** m = ⌊(r−1040)/2400⌋ ≥ (r−3440)/2400 ≥ a/2 for r ≥ 3440+1200a.
- **Upper bound.** Corollary A1 with n = 4r+1. TRUE.

**The refuted_by edit** on `elementary-group-lef-growth-separates-subshifts`. As a conjunction, the claim is false: it says the return-time function determines the LEF growth class, and that the class separates Diophantine types. The node keeps the isomorphism question open in Attempts. Correct.

PASS.
