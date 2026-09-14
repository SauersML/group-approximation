# sk-free-4: finite simple shadows (part 2: which sizes occur, and the rational spectrum)

Lane sk-free-4, 2026-09-13. Status: established with complete proofs below, UNREVIEWED (queued with sk-verify-13).

## 0. Setting
- A is a finite alphabet and T the left shift, (Tx)_n = x_{n+1}. X ⊆ A^Z is an infinite subshift that is **admissible**: every word graph W_r(X) is strongly connected. W_r(X) has vertices L_r(X) and edges L_{r+1}(X), each edge going from its length-r prefix to its length-r suffix. Every infinite minimal subshift is admissible (`research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md` §3).
- F = F_2⟨τ_+, τ_-, τ_a : a ∈ A⟩ is the free algebra, and π: F → R_X = LC(X,F_2)⋊Z is given by τ_± ↦ u^{±1}, τ_a ↦ e_a = 1_{[x_0=a]}.
- **Ring model through degree d, of size N:** a unital ring homomorphism ρ: F → M_N(F_2) with ker π ∩ F_{≤d} ⊆ ker ρ, i.e. every relation of R_X of degree ≤ d holds. It is **faithful through degree d** if also ρ(p) ≠ 0 for p ∈ F_{≤d} ∖ ker π.
- Periodic-word models: for a primitive cyclic word z ∈ A^N, ρ_z(τ_+) = P (cyclic shift), ρ_z(τ_-) = P^{-1}, ρ_z(τ_a) = D(z_a), the diagonal indicator of the letter a. These are onto M_N(F_2) (four-regular artifact §1), and faithful through degree d as soon as N > 2d and L_{2d+1}(z^∞) = L_{2d+1}(X) (same artifact §4).
- **Marked groups:** G_X = EL_3(R_X), marked by e_ij(1) and e_ij(π(τ)); approximants SL_{3N}(F_2), marked by e_ij(1) and e_ij(ρ(τ)).

## 1. The period of the word graphs is the rational spectrum

For a strongly connected finite directed graph W let per(W) be the gcd of the lengths of its closed walks. Put g_r = g_r(X) = per(W_r(X)).

**Lemma C1.**
- (a) g_r | g_{r+1}.
- (b) For m ≥ 1 the following are equivalent:
  - (i) there is a continuous T-equivariant map f: X → Z/m, with f(Tx) = f(x)+1;
  - (ii) e^{2πi/m} is a continuous eigenvalue of (X,T);
  - (iii) m | g_r for all large r.
- (c) So the finite divisors of the supernatural number g_∞(X) = lcm_r g_r are exactly the orders of the finite cyclic factors of X. Moreover g_∞ = 1 iff X is totally minimal (T^m minimal for every m), when X is minimal.

*Proof.*
- **Grading.** If W is strongly connected with period g, there is c: V(W) → Z/g with c(target) = c(source)+1 on every edge. This is the standard cyclic decomposition of an irreducible nonnegative matrix: fix a base vertex v, and set c(w) = the length mod g of any walk v → w, which is well defined because two such walks, closed up by a fixed walk w → v, give closed walks of lengths ≡ mod g. Conversely such a grading mod m forces m | every cycle length, so m | g.
- **(b)(iii) ⇒ (i).** With the grading c of W_r, put f(x) = c(x_{[0,r)}). The edge x_{[0,r]} goes from x_{[0,r)} to x_{[1,r+1)} = (Tx)_{[0,r)}, so f(Tx) = f(x)+1. Since m | g_r, reduce mod m.
- **(i) ⇒ (iii).**
  - f is continuous with finite image, so it depends on x_{[−s,s]} for some s.
  - f′(x) = f(T^s x) − s depends on x_{[0,2s]} and satisfies f′(Tx) = f′(x)+1.
  - For r ≥ 2s+1, f′ is a function of the r-block. It increases by 1 along each edge of W_r, since f′(Tx) = f′(x)+1 and every edge occurs in some point.
  - So m | the length of every closed walk, i.e. m | g_r.
- **(a).** Apply (i) ⇒ (iii) to the grading of W_r, which is a function of the r-block, at level r+1. (No shift is needed, since it already depends on x_{[0,r)}.)
- **(i) ⇔ (ii).**
  - (i) ⇒ (ii): h = e^{2πi f/m} is a continuous eigenfunction.
  - (ii) ⇒ (i): h∘T = e^{2πi/m}h forces |h| constant by minimality (|h| is continuous and T-invariant). Then h^m is continuous and T-invariant, hence constant, so h takes values in a finite set, which is a coset of μ_m. Take f with h = c·e^{2πif/m}. For admissible nonminimal X use (i) as the definition.
- **(c).** The first sentence is (b). For minimal X, T^m is not minimal iff there is a nontrivial cyclic factor of some order dividing m (standard: a T^m-minimal set Y, and X = Y ∪ TY ∪ … ∪ T^{m−1}Y, a disjoint union of clopen sets for the least such period). ∎

## 2. Which sizes occur

**Theorem C.**
- (1) **Necessity.** Let f: X → Z/m be a cyclic factor depending on x_{[0,r)}. Every ring model of R_X through degree 2r+1 has size N ≡ 0 mod m.
- (2) **Sufficiency.** For every r there is N_0(r) such that for every N ≥ N_0(r) with g_r | N there is a primitive cyclic word z of length N with L_{r+1}(z^∞) = L_{r+1}(X). The periodic-word model ρ_z is then onto M_N(F_2), and faithful through degree d whenever 2d+1 ≤ r+1 and N > 2d.

*Proof of (1).*
- Let E_i ∈ LC(X,F_2) be the indicator of f^{-1}(i). It is a sum of products of the indicators u^{-j}e_a u^{j} = 1_{[x_j=a]}, 0 ≤ j < r. So E_i = π(q_i) with q_i ∈ F of degree ≤ 2r−1, built from τ_-^{j}τ_aτ_+^{j} (check the convention in §0: u e_U u^{-1} = e_{TU}, so u^{-j}e_au^{j} is the indicator of {x_j = a}).
- In R_X these relations hold:
  - q_iq_j = δ_{ij}q_i, Σ_i q_i = 1;
  - τ_+τ_- = τ_-τ_+ = 1;
  - τ_+ q_i τ_- = q_{i−1}, indices mod m. The last holds because u E_i u^{-1} is the indicator of T(f^{-1}(i)) = f^{-1}(i+1), up to the sign convention of T; either orientation suffices.
- All these have degree ≤ 2r+1. So in a ring model ρ through degree 2r+1:
  - P = ρ(τ_+) is invertible;
  - the ρ(q_i) are orthogonal idempotents with sum I;
  - P ρ(q_i) P^{-1} = ρ(q_{i∓1}).
- Conjugate idempotents have equal rank, so N = m·rank ρ(q_0). ∎

*Proof of (2).*
- W = W_r(X) is strongly connected with period g = g_r. Fix a vertex v.
- **Covering walk.** There is a closed walk C at v traversing every edge (concatenate walks through all edges, using strong connectivity).
- **All large multiples.** The set S_v of lengths of closed walks at v is additively closed with gcd g, so it contains every sufficiently large multiple of g (Schur). Let k_0 g be a bound.
- **Many walks.** X is infinite, so W is not a single directed cycle (a cycle graph forces X finite; four-regular artifact §3, complexity argument). So the adjacency matrix of W has spectral radius Λ > 1, and by Perron–Frobenius for the primitive block of W^g, c_n := #{closed walks at v of length n} satisfies c_{kg} ≥ α Λ^{kg} for large k, with α > 0.
- **Non-powers.**
  - For N ≡ 0 mod g, the closed walks C·D, with D a closed walk at v of length N − |C| (note |C| ∈ S_v, so N − |C| ≡ 0 mod g), are pairwise distinct and all cover every edge. There are c_{N−|C|} ≥ αΛ^{N−|C|} of them for large N.
  - A closed walk at v of length N that is a proper power is Z^j for a closed walk Z at v of length N/j, j ≥ 2. There are at most Σ_{p | N prime} c_{N/p} ≤ log_2(N)·β Λ^{N/2} of them, using c_n ≤ βΛ^n.
  - For N large, some C·D is not a proper power.
- **Spelling.** Spell a closed walk as the cyclic word of the last letters of its edges. Its cyclic (r+1)-windows are exactly the traversed edges, and the walk is recovered from the word and the start vertex v.
  - A cyclic word z = y^j of length N, read from the position of v, returns to v after N/j steps: the vertex is the r-block ending there, which equals the r-block at step N. So the walk is a proper power.
  - Hence the word of a non-power walk is primitive, of least period N.
- **Models.** L_{r+1}(z^∞) is the set of traversed edges, i.e. L_{r+1}(X). The model statements are those of the four-regular artifact §§1, 4. ∎

**Corollary C2 (limits along a prescribed sequence).** Let N_k → ∞. The following are equivalent:
- (a) there are ring models ρ_k of size N_k, onto M_{N_k}(F_2) and faithful through degrees d_k → ∞, so that (SL_{3N_k}(F_2), e_ij(1), e_ij(ρ_k τ)) → (G_X, e_ij(1), e_ij(πτ)) in the space of marked groups;
- (b) for every finite cyclic factor order m of X, m | N_k for all large k; equivalently N_k → 0 in the supernatural sense of g_∞(X).

In particular G_X is a marked limit of the FULL sequence (SL_{3N}(F_2))_{N≥1}, with elementary markings over ring models, iff X has no nontrivial finite cyclic factor, iff (for minimal X) X is totally minimal.

*Proof.*
- **(b) ⇒ (a).** Put r_k = max{r ≤ k : g_r | N_k and N_k ≥ N_0(r)}. For fixed r, g_r is a cyclic factor order (Lemma C1), so r_k ≥ r for large k, and r_k → ∞. Take z_k from Theorem C(2) at level r_k, with d_k = ⌊r_k/2⌋. Faithfulness through degree d_k gives agreement of all group relations of length ≤ d_k (the note's degree argument: the entries of a word of length λ in the marking have degree ≤ λ, and a group word is trivial iff its entries minus I vanish).
- **(a) ⇒ (b).**
  - Fix m and f depending on x_{[0,r)}. The ring relations of §2(1) are entries of finitely many group relators of G_X, namely e_12(p) = 1 for the finitely many p = q_iq_j − δ_{ij}q_i, Σq_i − 1, τ_+q_iτ_- − q_{i∓1} (and invertibility through e_12 of τ_+τ_- − 1). Each e_12(p) is a word of bounded length in the marking (nested commutators, `subshift-algebra-groups-embed-in-marked-groups-proof`).
  - For large k these relators hold in the approximant. e_12(ρ_k(p)) = I iff ρ_k(p) = 0.
  - So ρ_k is a ring model through the needed degree on these finitely many elements, and the proof of Theorem C(1) uses only them. So m | N_k. ∎

**Examples.**
- **Sturmian subshifts** (irrational rotations; Fibonacci): no rational eigenvalue except 1, so G_X is the limit of SL_{3N}(F_2) along every N → ∞.
- **Thue–Morse subshift:** the continuous eigenvalues include all 2-power roots of unity (odometer factor Z_2). So G_X is a limit along N_k only when 2^n | N_k eventually for every n.
- **Toeplitz subshifts** with period structure (p_n): only along N_k divisible by each p_n eventually.

**Remark C3 (scope, and what stays open).**
- Theorem C and Corollary C2 concern ring-type approximants, the kind all known constructions use.
- Whether EVERY sequence of marked finite groups SL_{3N_k}(F_2) converging to G_X (any marking) forces m | N_k is the type-rigidity question T3 of the plan. A positive answer would make the rational spectrum of X an isomorphism invariant of the abstract group G_X, read off from the sizes of its finite simple shadows.
- Part 3 records the state of that question.
