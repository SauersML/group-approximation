# sk-verify-14, part 2: review of sk-free-4 part 2 (model sizes and the rational spectrum) and of sk-free-3 (conjugacy problem) (2026-09-13)

Lane sk-verify-14 (queue `sk/queue/sk-verify-13.txt`, lines 12–17). Every step was re-derived by hand. No other review of these claims was on main when I started.

## 0. Verdicts

| claim | verdict |
|---|---|
| `subshift-group-model-sizes-see-rational-spectrum` (sk-free-4 part 2: Lemma C1, Theorem C, Corollary C2) | **PASS WITH FIXES.** F1 corrects the degree bound in Theorem C(1); it is applied to the claim node and the route. |
| `subshift-el-transvection-conjugacy-full-group-equivalence` (sk-free-3 part 1: Lemma K, Lemma U) | **PASS.** W1 is a wording change to one consequence, applied to the claim node. |
| `subshift-elementary-group-conjugacy-degree-is-jump` (sk-free-3 part 2: Theorem CP) | **PASS** |

No FAIL.

## 1. sk-free-4 part 2

### 1.1 Lemma C1 (the word-graph period is the rational spectrum)
- **Grading.** Fix a base vertex and set c(w) = the length mod g of any walk to w. Two walks to w, closed up by a fixed walk back, have lengths congruent mod g. Conversely a Z/m-grading forces m | every cycle length, so m | g.
- **(iii) ⇒ (i).** Put f(x) = c(x_{[0,r)}) mod m. The edge x_{[0,r]} runs from x_{[0,r)} to x_{[1,r+1)} = (Tx)_{[0,r)}, so f(Tx) = f(x)+1.
- **(i) ⇒ (iii).**
  - f′ = f∘T^s − s depends on x_{[0,2s]} and satisfies f′∘T = f′+1.
  - For r ≥ 2s+1, f′ is a function on vertices that increases by 1 along every edge, because every edge occurs in a point. So m divides every closed-walk length.
- **(a).** The level-r grading, read on the prefix, grades W_{r+1}. So g_r | g_{r+1}.
- **(i) ⇔ (ii) for minimal X.**
  - |h| is continuous and T-invariant, hence constant.
  - h^m is invariant, hence constant, so h takes values in c·μ_m.
- **(c).** For minimal X, suppose T^m is not minimal, and let Y be T^m-minimal. The translates T^iY, for i up to the least p with T^pY = Y, partition X into clopen sets, which gives a cyclic factor of order p > 1. Conversely, a cyclic factor of order m > 1 gives a proper clopen T^m-invariant set.

### 1.2 Theorem C(1), necessity, and fix F1
The idempotent argument is correct:
- the ρ(q_i) are orthogonal idempotents with sum I;
- P = ρ(τ_+) is invertible;
- P ρ(q_i) P^{-1} = ρ(q_{i+1});
- so all ranks are equal and N = m · rank ρ(q_0).

f(Tx) = f(x)+1 makes every residue occur. With u 1_U u^{-1} = 1_{TU}, one has u E_i u^{-1} = E_{i+1}. The artifact's "q_{i−1} up to convention" does not affect the argument.

**F1, the degree bound.**
- **The error.** The artifact says E_i = π(q_i) with q_i of degree ≤ 2r−1, and that the relations used have degree ≤ 2r+1. That is false for r ≥ 2.
- **The correct form.** The cylinder indicator is 1_{[x_{[0,r)}=v]} = ∏_{j<r} u^{-j}e_{v_j}u^{j} = e_{v_0}u^{-1}e_{v_1}u^{-1}⋯u^{-1}e_{v_{r−1}}u^{r−1}, of degree 3r−2.
- **Why 3 is impossible at r = 2.** An element of u-degree 0 that detects x_1 needs a factor u^{-1}e_bu, plus e_a for x_0, which is degree 4.
- **The relations used.** Their degrees are:
  - q_iq_j − δ_{ij}q_i: at most 6r−4;
  - Σ_iq_i − 1: at most 3r−2;
  - τ_+q_iτ_- − q_{i+1}: at most 3r;
  - τ_+τ_- − 1 and τ_-τ_+ − 1: 2.

  So the threshold is 6r−4, which is ≥ 2 for every r ≥ 1.
- **Verbatim fixes to the artifact (§2).**
  - (1): "Every ring model of R_X through degree 2r+1 has size N ≡ 0 mod m." becomes "Every ring model of R_X through degree 6r−4 has size N ≡ 0 mod m."
  - Proof: "So E_i = π(q_i) with q_i ∈ F of degree ≤ 2r−1, built from τ_-^{j}τ_aτ_+^{j}" becomes "So E_i = π(q_i), where q_i ∈ F is a sum of the monomials τ_{v_0}τ_-τ_{v_1}τ_-⋯τ_-τ_{v_{r−1}}τ_+^{r−1}, of degree 3r−2".
  - "All these have degree ≤ 2r+1." becomes "All these have degree ≤ 6r−4."
- **Applied on main:** claim item 2 ("through degree `6r−4`") and route bullet "Necessity" ("of degree `≤ 3r−2`").
- **Scope.** Corollary C2 is unaffected. Its (a) ⇒ (b) uses only finitely many relators e_12(p) = 1 of bounded length, and (b) ⇒ (a) uses Theorem C(2).

### 1.3 Theorem C(2), sufficiency
Checked:
- the covering closed walk C;
- the closed-walk lengths at v form a semigroup with gcd g, so all large multiples of g occur (Schur);
- X infinite forces W not to be a directed cycle, so Λ > 1;
- Perron–Frobenius on the primitive block gives c_{kg} ≥ αΛ^{kg}, and c_n ≤ βΛ^n;
- the count of the walks C·D, at least αΛ^{N−|C|}, beats the at most log_2(N)·βΛ^{N/2} proper powers.

The spelling step also holds:
- The r-block of the cyclic word ending at step i is the i-th vertex, so the cyclic (r+1)-windows are the traversed edges.
- If z = y^j, the walk returns to v after N/j steps and repeats, so a non-power walk spells a primitive word.
- L_{r+1}(z^∞) is the set of traversed edges, which is L_{r+1}(X).

### 1.4 The two model facts the route imports
The route requires `four-regular-simple-expander-limits-encode-word-graphs`, which has no review line on main. The verdict does not rest on it, because the two facts used were re-derived here.
- **Onto.** For primitive z, the products ∏_{j<N} P^{j}D(z_{a_j})P^{-j} pick out single positions, since distinct rotations are distinct. So all diagonal matrix units lie in the algebra, and with P they give M_N(F_2).
- **Faithful through degree d.** For p ∈ F_{≤d}, π(p) = Σ_{|k|≤d} f_k u^k, with f_k depending on x_{[−d,d]}. Then ρ_z(p) = Σ_k D(f_k)P^k, with f_k evaluated on the windows of z^∞.
  - If N > 2d, the diagonals of P^k, |k| ≤ d, are disjoint.
  - So ρ_z(p) = 0 iff every f_k vanishes on L_{2d+1}(z^∞) = L_{2d+1}(X), iff π(p) = 0.

### 1.5 Corollary C2
- **(b) ⇒ (a).** For fixed r, g_r is a cyclic factor order, so g_r | N_k eventually, and r_k → ∞. Take d_k = ⌊r_k/2⌋. Faithfulness through degree d_k makes group words of length ≤ d_k agree, since entries of such words have degree ≤ d_k and e_12(x) = I iff x = 0.
- **(a) ⇒ (b).** The same word w_p computes e_12(π(p)) in G_X and e_12(ρ_k(p)) in the approximant, because the commutator identities hold in EL_3 over any ring receiving F. So finitely many ring relations hold for large k, and m | N_k.
- **"Full sequence iff totally minimal"** follows from Lemma C1(c).
- **Examples.** Sturmian (no rational eigenvalue except 1) and Thue–Morse (2-power roots of unity) are consistent.

## 2. sk-free-3 part 1: Lemma K and Lemma U

### 2.1 (c) ⇒ (a)
- **Intertwining.** With U_k = {n = k} and w = Σ_k 1_{γU_k}u^k: on γU_k one has γ^{-1} = T^{-k}, so w f = (f∘γ^{-1}) w.
- **w w′ = 1**, since T^kU_k ∩ T^kU_l = ∅ for k ≠ l and the sets γU_k partition X.
- **w′ w = 1.** A point of U_l ∩ T^{k−l}U_k has γx = γy with x = T^{k−l}y, so x = y and k = l.
- **Conjugation.** w 1_A w^{-1} = 1_{γA} = 1_B.
- **Whitehead identity**, checked in M_2 over a noncommutative ring of characteristic 2:
  - e_12(c)e_21(c^{-1}) = [[0,c],[c^{-1},1]];
  - times e_12(c) this is [[0,c],[c^{-1},0]];
  - times [[0,1],[1,0]] = e_12(1)e_21(1)e_12(1) this is diag(c,c^{-1}).
- **The conjugator.** k = diag(w,w^{-1},1)·diag(1,w^{-1},w) = diag(w,w^{-2},w) ∈ G_X, and diag(a,b,c)e_13(r)diag(a,b,c)^{-1} = e_13(a r c^{-1}).
- **No false map is used:** neither diag(a,a^{-1},1) as a homomorphism nor the double swap.

### 2.2 (b) ⇒ (c)
- g is locally constant, so there is a clopen base Z on which g is constant.
- Return times are finite, continuous and bounded.
- The partition Z_{h,β} makes each level lie inside A or its complement, and inside B or its complement.
- The tower sum Σ_{j<h} f(T^jz) = g(T^hz) − g(z) = 0 equalizes the A-levels and B-levels.
- The level permutation σ defines γ ∈ [[T]] with γA = B.

### 2.3 (a) ⇒ (b), route 1
- **Multiplicativity.** φ is well defined on the unique representation Σ f_j u^j. It is multiplicative on the finitely many products in k·(I+E_13 1_A) = (I+E_13 1_B)·k and k·k^{-1} = I, because those products need radius ≤ ρ+λ ≤ ℓ. The stated ℓ ≥ ρ+4λ+1 has room to spare.
- **Rank equality.** It gives Σ_{t∈Z/N}(1_A − 1_B)(y^{(t)}) = 0.
- **Loop words.** If x[a,a+L) = x[b,b+L), the (b−a)-periodic word y satisfies y[0,b−a+L) = x[a,b+L). This holds by induction on the index, including when L > b−a. So every L-window of y lies in L(X). The windows at t ∈ [ℓ, ℓ+b−a) are those of T^{a+t}x.
- **Transfer function.** The sums telescope to S(a+ℓ) = S(b+ℓ). G is well defined and defined on all of L_L(X), because the forward orbit is dense. g(T^kx) = S(k) for k ≥ ℓ, and continuity plus density give g∘T − g = f.
- **Independence.** Route 2 (K_0) is a consistent cross-check that uses `subshift-crossed-product-k0-is-coinvariant-group` (PASS at group level). Route 1 does not need it.

### 2.4 Lemma U and Corollary K
- **Lemma U.** Yes-instances of CP are Σ^0_1 relative to WP, and Σ^0_1(S) ≤_T S′. With WP ≡_T L(X), this gives CP ≤_T L(X)′. Also WP ≤_T CP.
- **Corollary K.** Words for e_13(1_A) are computable from a cylinder list, by additivity of e_13 and the cylinder products.

### 2.5 W1 (wording, applied to the claim node)
- **Current text.** "The root-transvection conjugacy classes `e_13(1_A)` are exactly the classes `[1_A]` of `K^0(X,T)` between `0` and `[1]`."
- **The problem.** This can be read as saying that every element of the order interval [0,[1]] is the class of a clopen set. That realization fact is neither proved nor cited in the lane.
- **Replacement.** "The conjugacy classes of the root transvections `e_13(1_A)` correspond bijectively to the classes `[1_A]` (`A` clopen) in `K^0(X,T)`."

## 3. sk-free-3 part 2: Theorem CP

Checked in order:
- **Alphabets and morphisms.**
  - H(e,m) is monotone in m, so E_{m+1} ⊆ E_m ∪ {m}.
  - The payloads have one common length, contain no s, and are pairwise distinct (carriers start with their letter; the fixed and entering payloads are w^p, tw^{p−1}, wtw^{p−2}, wwtw^{p−3}, wwwtw^{p−4}).
  - |τ_m(c)| = ℓ_m is constant.
  - p_m ≥ 5 must be a fixed computable sequence (for example p_m = 5). The artifact leaves it implicit, which is harmless.
- **(P0) and nonemptiness.** B_{M+2}(s) contains B_{M+1}(s) inside the marker and inside W = w s t…, with full blocks on both sides.
- **(P1) Recognizability.** The letter s occurs only in markers (runs ≥ 2, preceded by t, followed by a non-s payload letter) and once in W_m, between w and t. So maximal runs of at least two s are exactly the markers. τ_m is injective, and uniqueness of decompositions follows by induction.
- **(P2) Minimality.** W_m lists Σ_m, so every B_{m+1}(c) contains every B_m(c′). Aperiodicity holds because the boundaries are locally determined, which forces L_m | p for every m.
- **(P3) L(X) ≤_T S.** A word of length ≤ L_m lies in two consecutive level-m blocks: either inside one level-(m+1) block, or B_m(t)B_m(s). B_{m+2}(s) contains W_{m+1} = w s t…, hence that pair and every B_{m+1}(c).
- **(P4) S ≤_T L(X).**
  - k_m = 2 gives runs of s of length ≤ 2, while k_m = 3 produces "t s s s".
  - Continuing carriers show up as s^{k_m}x_e w.
  - The entering pair shows up as s^{k_m}wwt, which no other payload starts with.
- **(P5).** A_e and B_e are clopen, and if H(e,e) they are empty.
- **The counting claim.**
  - Base case as stated.
  - Step: s, t and w contribute 0, x_e and y_e contribute ±1, and W contains each exactly once.
  - Retirement: no payload carries x_e or y_e, and d_m(W_m) = 0.
- **(P6).** For g = the count over [b,0), the non-boundary case gives g(Tx) = g(x) + f_e(x). The boundary case gives g(Tx) = 0 = d_{m+1}(c). With (Tx)_i = x_{i+1}, f_e = g∘T − g.
- **(P7).** Suppose g has radius r < L_m. At every level-(m+1) boundary the window is (end of B_m(t))(start of B_m(s)), so block sums vanish. But a block of x_e has sum 1, and x_e ∈ Σ_{m+1} occurs in every x. Contradiction.
- **§4.**
  - S′ ≤_T CP: from a CP oracle compute S (S ≤_T WP ≤_T CP), then the cylinder words, then query CP. By Lemma K, e ∈ S′ iff the pair is conjugate.
  - Upper bound: CP ≤_T L(X)′ ≡_T S′, since the jump is degree invariant.
  - For computable S, G_X is simple Kazhdan LEF (the note's Theorem 1) with solvable WP and CP of degree 0′.

**Dependency.** `subshift-elementary-group-word-problem-degree` has no review line on main. Its content is rev3 §3, which rev3 referee (a) re-derived line by line (`research/artifacts/sk-rev3-referee-a-2026-09-13.md` §1).

**Not checked.**
- Novelty: arXiv:2509.12161, and Šunić–Ventura arXiv:1010.1993, were not opened.
- The Glasner–Weiss / GPS locator for the tower argument; the proof in the artifact is self-contained.
- The firewall remark on Sturmian subshifts (decidable coboundary problem for computable slope). It is labelled a firewall, not a claim.
