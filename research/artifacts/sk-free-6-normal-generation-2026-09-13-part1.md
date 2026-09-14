# sk-free-6 part 1: invariant measures govern normal generation in G_X (2026-09-13)

Lane sk-free-6 (wave 10, free lane). Plan: `research/artifacts/sk-free-6-plan-2026-09-13.md`.

## 0. Setting and notation
- (X,T) is a minimal homeomorphism of an infinite Cantor set: every infinite minimal subshift, and more. R = R_X = LC(X,F_2) ⋊_T Z with unit u, u χ_W u^{-1} = χ_{TW}, and G = G_X = EL_3(R).
- M_T(X) is the simplex of T-invariant Borel probability measures. Each has full support, since X is minimal.
- For g ∈ G∖{e} and h ∈ G, ν_g(h) is the least N such that h = ∏_{i=1}^N x_i g^{ε_i} x_i^{-1} with x_i ∈ G and ε_i = ±1 (∞ if there is none). Put cw(g) = sup_h ν_g(h). G is *uniformly simple* when sup_{g≠e} cw(g) < ∞.
- For clopen U, V with V ≠ ∅: ρ_max(U,V) = sup_μ μ(U)/μ(V) and ρ_min(U,V) = inf_μ μ(U)/μ(V). Both are finite, because inf_μ μ(V) > 0 by compactness of M_T(X) and full support.

Facts used (all on main or in the note):
- (F1) **Commutator formula.** [e_ik(a), e_kj(b)] = e_ij(ab) for distinct i, j, k. Root subgroups are additive: e_ij(a)e_ij(b) = e_ij(a+b).
- (F2) **Whitehead in characteristic 2.** e_12(c)e_21(c^{-1})e_12(c) = [[0,c],[c^{-1},0]]. Times e_12(1)e_21(1)e_12(1) = [[0,1],[1,0]] this gives diag(c,c^{-1},1) ∈ G for every unit c ∈ R. The same holds in positions (2,3). Also diag(a,b,c) e_12(r) diag(a,b,c)^{-1} = e_12(a r b^{-1}).
- (F3) **Permutation matrices.** Over F_2 they lie in SL_3(F_2) = E_3(F_2) ⊆ G. The transposition P = P_(13) satisfies P e_12(r) P^{-1} = e_32(r).
- (F4) **Rank functions** (`cantor-z-crossed-product-embeds-in-continuous-factor`, Ara–Claramunt by citation). For every ergodic μ ∈ M_T(X), R has a faithful Sylvester matrix rank function rk_μ with rk_μ(χ_U) = μ(U).
- (F5) **Kakutani–Rokhlin partitions** (Herman–Putnam–Skau 1992, standard). For every L and every finite clopen partition 𝒬 of X, there are clopen bases B_1,…,B_J and heights h_j ≥ L such that the levels T^iB_j (0 ≤ i < h_j) partition X and each level lies in one atom of 𝒬. Route: take a clopen B with B ∩ T^iB = ∅ for 0 < i < L (X has no periodic points), then split B by first return time and by the 𝒬-itinerary along the return segment. Minimality bounds the return time, so there are finitely many pieces.
- (F6) **Faithful orbit representation.** R acts on ⊕_{x∈X} F_2[Z]: χ_W δ_n = 1_W(T^n x)δ_n and u δ_n = δ_{n+1}. This representation is faithful, so identities in R can be checked there.

## 1. Theorem A (rank lengths)
**Theorem A.** For ergodic μ ∈ M_T(X), put ℓ_μ(g) = rk_μ(g − I_3) for g ∈ G, with rk_μ extended to M_3(R).
1. ℓ_μ is conjugation-invariant, symmetric (ℓ_μ(g^{-1}) = ℓ_μ(g)) and subadditive (ℓ_μ(gh) ≤ ℓ_μ(g) + ℓ_μ(h)). It is faithful, taking values in [0,3].
2. ℓ_μ(e_ij(r)) = rk_μ(r). In particular ℓ_μ(e_12(χ_U)) = μ(U), so μ ↦ ℓ_μ is injective.
3. For every g ≠ e and h ∈ G, ν_g(h) ≥ ℓ_μ(h)/ℓ_μ(g).
4. **Corollary.** G is simple (for subshifts) but not uniformly simple: cw(e_12(χ_V)) ≥ ν_{e_12(χ_V)}(e_12(1)) ≥ 1/inf_μ μ(V), which tends to ∞ as V shrinks.

**Proof.**
1. Sylvester rank functions are invariant under multiplication by invertible matrices, since rk(xy) ≤ min(rk x, rk y).
   - Conjugation: x g x^{-1} − I = x(g − I)x^{-1}.
   - Symmetry: g^{-1} − I = −g^{-1}(g − I).
   - Subadditivity: gh − I = (g − I)h + (h − I) and rk(a + b) ≤ rk a + rk b.
   - Faithfulness is (F4), and rk_μ(I_3) = 3.
2. r E_ij = (r E_ii)·Π, where Π is the permutation matrix that maps e_j to e_i. Also rk_μ(r E_ii) = rk_μ(r), by rk(a ⊕ 0) = rk(a).
3. If h = ∏_{i≤N} x_i g^{±1} x_i^{-1}, then by 1, ℓ_μ(h) ≤ N ℓ_μ(g).
4. Apply 3 with h = e_12(1), g = e_12(χ_V), μ ergodic: ν ≥ 1/μ(V). The supremum over ergodic μ equals the supremum over M_T(X): μ ↦ μ(U)/μ(V) is a ratio of positive affine functions, so it is quasi-affine and attains its extrema on a compact simplex at extreme points. Nonatomic μ gives clopen V with μ(V) → 0. Simplicity of G for subshifts is the note's theorem (`finite-model-subshift-elementary-groups-simple-kazhdan-lef`). ∎

**Contrast.** Every extreme character of G is 1 or δ_e (`subshift-elementary-groups-are-character-rigid`), so traces see no measure. The rank lengths ℓ_μ are a whole simplex of bi-invariant length functions, one for each invariant measure.

## 2. Theorem B (normal generation numbers of transvections)
**Theorem B.** Let U, V ⊆ X be clopen, V ≠ ∅, and put ν = ν_{e_12(χ_V)}(e_12(χ_U)), ρ_max = ρ_max(U,V), ρ_min = ρ_min(U,V). Then

  ρ_max ≤ ν ≤ 2⌊ρ_max⌋ − ⌈ρ_min⌉ + 3.

- **Uniquely ergodic X, μ(U)/μ(V) = ρ:** ⌈ρ⌉ ≤ ν ≤ ⌊ρ⌋ + 3.
- **Recovery of μ.** If X is uniquely ergodic and V_n are clopen with μ(V_n) → 0, then for every clopen U

  μ(U) = lim_n ν_{e_12(χ_{V_n})}(e_12(χ_U)) / ν_{e_12(χ_{V_n})}(e_12(1)).

  The invariant measure is thus a limit of ratios of normal generation numbers in G_X.

**Proof of the lower bound.** Theorem A.3 with h = e_12(χ_U) and ergodic μ gives ν ≥ μ(U)/μ(V). Take the supremum over ergodic μ, as in A.4.

**Step 1 (uniform ratios).** For every δ > 0 there is L such that, for all x ∈ X and n ≥ L, the counts a = #{0≤i<n : T^ix ∈ U} and b = #{0≤i<n : T^ix ∈ V} satisfy b ≥ 1 and a/b ∈ [ρ_min − δ, ρ_max + δ].
- Otherwise take x_k and n_k → ∞ that violate this.
- A weak* limit μ of the empirical measures n_k^{-1} Σ_{i<n_k} δ_{T^i x_k} is T-invariant.
- χ_U and χ_V are continuous and μ(V) ≥ inf_μ μ(V) > 0, so the ratios converge to μ(U)/μ(V), which lies outside [ρ_min − δ, ρ_max + δ]. This is a contradiction.
- The same argument gives b ≥ 1.

**Step 2 (towers).** Assume U ≠ ∅ (if U = ∅ then ν = 0). Fix 0 < δ < 1 with δ < ⌈ρ_max⌉ − ρ_max if ρ_max ∉ Z, and δ < ρ_min − ⌊ρ_min⌋ if ρ_min ∉ Z. Take L from Step 1 and a Kakutani–Rokhlin partition (F5) with heights h_j ≥ L subordinate to {U, X∖U} ∧ {V, X∖V}.
- In tower j let I_j (a_j elements) and K_j (b_j elements) be the U-levels and V-levels.
- Apply Step 1 to x ∈ B_j and n = h_j: b_j ≥ 1 and a_j/b_j ∈ [ρ_min − δ, ρ_max + δ].
- With s_j = ⌊a_j/b_j⌋ and T_j = ⌈a_j/b_j⌉, the choice of δ gives s := min_j s_j ≥ ⌈ρ_min⌉ − 1 and T := max_j T_j ≤ ⌊ρ_max⌋ + 1.

**Step 3 (pieces).** List I_j in increasing order and cut it into consecutive groups Γ_{j,1},…,Γ_{j,T_j}: the first s_j groups have b_j levels, and the last group (if a_j/b_j ∉ Z) holds the remaining a_j − s_j b_j < b_j levels. Set Γ_{j,t} = ∅ for T_j < t ≤ T. Then define
- U_t := ⋃_j ⋃_{i∈Γ_{j,t}} T^iB_j, a clopen set, with U = ⊔_{t=1}^{T} U_t;
- V′_t := ⋃_j (the first |Γ_{j,t}| elements of K_j, as levels of tower j) ⊆ V.

For t ≤ s every tower has |Γ_{j,t}| = b_j, so V′_t = V.

**Step 4 (level permutations).** For each t and j pick a permutation σ_{j,t} of {0,…,h_j−1} that maps the first |Γ_{j,t}| elements of K_j onto Γ_{j,t}. Put

  w_t := Σ_j Σ_{0≤i<h_j} u^{σ_{j,t}(i) − i} χ_{T^iB_j} ∈ R.

In the orbit representation (F6), w_t moves δ_n, with T^n x ∈ T^iB_j, to δ_{n−i+σ_{j,t}(i)}. That is the same occurrence of tower j, at level σ_{j,t}(i). So w_t is a bijection of positions, with inverse w built from σ_{j,t}^{-1}. So w_t ∈ R^×, and w_t χ_{T^iB_j} w_t^{-1} = χ_{T^{σ(i)}B_j}. Hence w_t χ_{V′_t} w_t^{-1} = χ_{U_t}.

**Step 5 (conjugation).** D_t := diag(w_t, w_t, w_t^{-2}) = diag(w_t, w_t^{-1}, 1)·diag(1, w_t^2, w_t^{-2}) lies in G by (F2), and D_t e_12(χ_{V′_t}) D_t^{-1} = e_12(χ_{U_t}).

**Step 6 (count).** Put g := e_12(χ_V). By (F1), e_12(χ_U) = ∏_{t=1}^{T} e_12(χ_{U_t}).
- **t ≤ s:** V′_t = V, so e_12(χ_{U_t}) = D_t g D_t^{-1} is one conjugate.
- **s < t ≤ T:** by (F1), e_12(χ_{V′_t}) = [e_13(χ_{V′_t}), e_32(χ_V)], since χ_{V′_t}χ_V = χ_{V′_t}.
  - This commutator is x e_32(χ_V) x^{-1} · e_32(χ_V)^{-1} with x = e_13(χ_{V′_t}).
  - By (F3), e_32(χ_V) = PgP^{-1}. So e_12(χ_{V′_t}) is a product of two conjugates of g^{±1}.
  - Conjugating by D_t, so is e_12(χ_{U_t}).

So ν ≤ s + 2(T − s) = 2T − s ≤ 2⌊ρ_max⌋ + 2 − ⌈ρ_min⌉ + 1. ∎

**Uniquely ergodic case.** 2⌊ρ⌋ − ⌈ρ⌉ + 3 ≤ ⌊ρ⌋ + 3, and ν ≥ ⌈ρ⌉ because ν is an integer.

**Recovery.** The numerator is μ(U)/μ(V_n) + O(1) and the denominator is 1/μ(V_n) + O(1). Both tend to ∞, and the ratio tends to μ(U). ∎

**Model tests.**
- **2-adic odometer**, V a cylinder of level n, U = X: ρ = 2^n. The partition of X into the 2^n translates of V gives ν = 2^n exactly, consistent with [2^n, 2^n + 3].
- **Sturmian X_α** (uniquely ergodic), V = [1], U = X: ρ = 1/α, so 1/α ≤ ν ≤ ⌊1/α⌋ + 3.
- **Non-uniquely-ergodic minimal subshifts:** the bound keeps the gap ρ_max − ρ_min; the lower bound sees the worst measure.
- **Trivial model:** a periodic orbit (excluded, since it is not a Cantor space). There the ring is M_p(F_2[t^{±1}]) and Step 1 still holds, but μ is atomic and Corollary A.4 fails, as it should.

## 3. Corollary C (every element normally generates root elements boundedly)
**Corollary C.** Let X be an infinite minimal subshift. For every g ∈ G∖{e} there is M_g < ∞ such that every root element e_ij(r), r ∈ R, is a product of at most M_g conjugates of g^{±1}. With the constant M′_g below,

  M_g ≤ 2·(2⌊1/inf_μ μ(V_g)⌋ + 2)·M′_g.

**Proof.**
- The note's simplicity proof commutes g with a tower transvection. This gives k = [g, x] ≠ e, a product of 2 conjugates of g^{±1}, inside the embedded finite simple group H ≅ GL_d(F_2), d = 3(2w+1), over a small clopen V_g.
- H is finite and simple, so the H-normal closure of k is H. So e_12(χ_{V_g}) ∈ H is a product of at most c_H conjugates of k^{±1}, where c_H is a finite constant (for instance |H|).
- So M′_g := 2c_H conjugates of g^{±1} give e_12(χ_{V_g}).
- Theorem B with U = X: e_12(1) needs at most 2⌊ρ_max⌋ − ⌈ρ_min⌉ + 3 ≤ 2⌊1/inf_μ μ(V_g)⌋ + 2 conjugates of e_12(χ_{V_g}).
- Finally e_ij(r) = [e_ik(r), e_kj(1)] is 2 conjugates of e_kj(1)^{±1}, and e_kj(1) is a permutation conjugate of e_12(1) (F3). ∎

**Consequence (bi-Lipschitz norms).** Let λ^c(h) be the least number of conjugates of root elements whose product is h. It is finite, since G = E_3(R). Then λ^c(h) ≤ λ^c(g)·ν_g(h), because each conjugate of g is a product of λ^c(g) conjugates of root elements. Also ν_g(h) ≤ M_g·λ^c(h), by Corollary C. So all the normal generation norms ν_g (g ≠ e) and λ^c are pairwise bi-Lipschitz. G_X is *bounded* in the sense of Burago–Ivanov–Polterovich (every conjugation-invariant norm is bounded) iff λ^c is bounded.

## 4. Open D: is G_X bounded (every conjugation-invariant norm bounded)?
By C, this is equivalent to sup_h λ^c(h) < ∞. Bounded generation by root subgroups (G = ∏_{k≤m} e_{i_k j_k}(R)) would suffice.

**Reduction (cut lemma, sketch, to be written in part 2).** Let h ∈ G have propagation w. Take a Kakutani–Rokhlin cut system Y with heights ≫ w, and let A_Y be the orbit-breaking subalgebra (block-diagonal over towers, locally matricial).
1. **The index vanishes on G** (every root element is unipotent modulo finite rank, over F_2).
   - So each half-line compression of h is Fredholm of index 0.
   - The kernel and cokernel of the block compression P_B h P_B are localized within w′ of the two ends of B, where w′ bounds the propagation of h^{-1}.
   - The index at each end is 0.
2. **Correct end by end,** with locally constant choices on the finitely many local types. This gives H_1 ∈ GL_3(A_Y) = EL_3(A_Y), with h − H_1 supported in bands around the cuts.
   - By block Gauss reduction over the finite products ∏ M_{h_j}(F_2) (stable rank 1) plus Thompson's theorem (every element of SL_m(F), m ≥ 3, is a commutator), H_1 is a product of at most 28 root elements.
3. **h = H_1(I + X) with X = Xp,** where p = χ_W and W is the band.
   - Then I + X = (I + (1−p)Xp)(I + pXp).
   - The first factor is a product of at most 18 root elements: off-diagonal entries directly, and diagonal entries through [e_ik(y), e_ki(p)] = I + yE_ii for y ∈ (1−p)Rp.
4. **Remaining factor:** I + pXp ∈ GL_3(e_W R e_W) ∩ G. It has propagation ≤ 1 in the induced system on W, because H_1^{-1} can carry a band at the top of a block to the band at its bottom.
   - Example: diag(u, u^{-1}) gives the induced Whitehead element diag(u_W, u_W^{-1}), which is 6 root elements.
   - So λ(h) ≤ 46 + λ(remainder), and **Open D reduces to bounded root length for degree-≤1 elements over induced systems.**

**Where it stands.**
- Iterating the cut lemma on the remainder does not terminate: the corrected compressions have inverses that wrap around blocks.
- A Euclid-type reduction in the induced degree needs control of the leading coefficients (regular but not invertible), which is the sr(R_X) = 1 question.
- If sr(R_X) = 1, a unimodular column reduces to e_1 with at most 6 root elements, and GL_3(R) = (at most 10 root elements)·diag(1,1,GL_1(R)). Open D then reduces to: an index-0 unit v has diag(1,1,v) of bounded root length.
- sr(R_X) = 1 is equivalent to internal cancellation for the exchange ring R_X (Yu 1995, recalled; `minimal-cantor-crossed-product-is-an-exchange-ring`). So it would follow from V(R_X) ≅ K^0(X,T)^+.

**Also relevant.**
- `subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology`: H_b^k with mixing coefficients vanishes. That does not address trivial coefficients or quasimorphisms. Boundedness would kill all homogeneous quasimorphisms, which (T) alone does not.

## 5. Credit and novelty (bounded)
- **Operator-algebraic analogues** (abstracts read on arXiv 2026-09-13):
  - P. A. Dowerk and A. Thom, "Bounded normal generation and invariant automatic continuity", arXiv:1506.08549 (journal version in Adv. Math., ScienceDirect S0001870819300830). The abstract says it studies "how quickly products of a fixed conjugacy class in the projective unitary group of a II₁-factor von Neumann algebra cover the entire group". The number of factors is essentially as small as the 1-norm permits, in analogy with Liebeck–Shalev for finite simple groups.
  - P. A. Dowerk and A. Thom, arXiv:1606.00409: the same question for the Calkin algebra and type III factors.
  - An earlier draft of this artifact attributed 1506.08549 to Dowerk–Le Maître and to full groups; that was wrong and is corrected here.
  - Theorem B is the topological-algebraic analogue for G_X: the rank functions of R_X play the role of the trace, and Kakutani–Rokhlin towers replace measurable Rokhlin lemmas.
- **Topological full groups:** Matui, "Some remarks on topological full groups of Cantor minimal systems" (arXiv:math/0404117), studies normal subgroups and saturation. The search found no normal generation numbers there.
- **Towers:** Herman–Putnam–Skau. **Rank functions:** Ara–Claramunt.
- **Search bound:** a grep of main for "uniformly simple", "normal generation", "conjugation-invariant norm", "bounded generation" and "commutator width" found no node on these for G_X or for subshift crossed products. No web search yet; one is planned before the proposal.

## 6. Nodes planned (land after the disk hold lifts)
- `subshift-el-rank-lengths-force-non-uniform-simplicity` (A) plus `-proof`, requires [cantor-z-crossed-product-embeds-in-continuous-factor, finite-model-subshift-elementary-groups-simple-kazhdan-lef].
- `transvection-normal-generation-recovers-invariant-measures` (B) plus `-proof`, requires [subshift-el-rank-lengths-force-non-uniform-simplicity].
- `subshift-el-root-elements-boundedly-normally-generated` (C) plus `-proof`, requires [transvection-normal-generation-recovers-invariant-measures, finite-model-subshift-elementary-groups-simple-kazhdan-lef].
- `subshift-el-groups-have-bounded-conjugation-invariant-norms` (D, OPEN, with Attempts).
