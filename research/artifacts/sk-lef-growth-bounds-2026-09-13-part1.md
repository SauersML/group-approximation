# sk-lef-growth: LEF growth of the simple Kazhdan groups G_X (part 1: definitions and general bounds)

Lane sk-lef-growth, 2026-09-13. Status: written proofs, UNREVIEWED (queued with sk-referee-2).
Part 2 has the Sturmian theorem (exp(Θ(r²)) for every slope), the consequences and the literature bound.

## 0. Setting
- X ⊆ A^Z is an infinite minimal subshift, with shift (Tx)_n = x_{n+1}. R = LC(X,F_2) ⋊_T Z, with u f u^{-1} = f∘T^{-1}, and G_X = EL_3(R).
  This is the group of the note (`$SK/manuscript-disk-1646.tex` l.44-53).
- S = { e_ij(s) : i ≠ j, s ∈ {1, u, u^{-1}} ∪ {e_a : a ∈ A} }, the generating set of the note (l.94-95).
  Every element of S is an involution. |g| is the word length and B(r) is the ball.
- **LEF growth** (Bradford, arXiv:2104.07111; Bradford–Dona, arXiv:2106.09145; the same definition as the main node
  `elementary-group-lef-growth-separates-subshifts`):
  `L_X(r) = min{ |Q| : Q finite, ∃ φ: B(r) → Q injective with φ(gh) = φ(g)φ(h) whenever g, h, gh ∈ B(r) }`.
- Comparison: f ≼ g iff f(r) ≤ g(Cr) for some C and all r, and ≃ means both ways. Changing the generating set changes r by a
  bounded factor, so the ≃-class of L_X is an isomorphism invariant of G_X.
- Dynamical functions:
  - p_X(n) = |L_n(X)|, the complexity;
  - R_X(n), the least m such that every word of X of length m contains every word of X of length n;
  - N_X(n), the least length of a cyclic word whose cyclic windows of length n are exactly L_n(X).

**Lemma 0 (relations transport).** Let φ be as in the definition and s_1⋯s_ℓ a word with ℓ ≤ r. Then
φ(s_1⋯s_ℓ) = φ(s_1)⋯φ(s_ℓ). In particular every relation of G_X of length ≤ r holds among the φ(s), s ∈ S.
*Proof.* All prefixes lie in B(r), so the claim follows by induction. Also φ(1) = φ(1)², so φ(1) = 1. ∎

## 1. Upper bound
**Theorem A.** For every infinite minimal X and every r ≥ 1,
`L_X(r) ≤ |GL_{3N}(F_2)| < 2^{9N²}`, where `N = N_X(4r+1)`,
and `N_X(n) ≤ min{ 2R_X(n), (p_X(n)+1)·p_X(n−1) }`.

*Proof.*
(a) *Windows.* An entry of g ∈ B(r) is a sum of products s_1⋯s_ℓ with ℓ ≤ r and s_t ∈ {0, 1, u, u^{-1}, e_a}.
- Moving the powers of u to the right turns each e_a into e_a∘T^{-c} with |c| ≤ ℓ−1. That is the indicator of
  {x_{-c} = a}. So each entry is Σ_{|j|≤r} f_j u^j, with every f_j depending only on x_{[−r,r]}.
- The matrix product of two elements of B(r) uses the ring products f u^i · f' u^j = f·(f'∘T^{-i}) u^{i+j}, and their windows lie in [−2r, 2r].

(b) *Model.* Let y be a cyclic word of length N whose cyclic windows of length 4r+1 are exactly L_{4r+1}(X).
- On F_2^{Z/NZ}, put Pδ_n = δ_{n+1}. For f with window [−ρ,ρ], ρ ≤ 2r, put D(f)δ_n = f(y_{[n−ρ,n+ρ]})δ_n.
- D is well defined, because the windows of y are words of X. It satisfies D(f)D(f') = D(ff') and PD(f)P^{-1} = D(f∘T^{-1}) whenever the windows stay ≤ 2r.
- Define φ entrywise by Σ f_j u^j ↦ Σ D(f_j)P^j. By (a), φ(gh) = φ(g)φ(h) for g, h, gh ∈ B(r). Since g^{-1} ∈ B(r), φ(g) is invertible.
- *Injectivity.* If g ≠ h, some entry of g − h has an f_j ≠ 0 with window ≤ r. It equals 1 on a word of length 2r+1, and that word occurs in y, so D(f_j) ≠ 0.
  Also N ≥ p_X(4r+1) ≥ 4r+2 > 2r, so the exponents |j| ≤ r are distinct mod N and φ(g) ≠ φ(h).
- This is the note's l.131-149 with the windows made explicit.

(c) *N_X(n) ≤ 2R_X(n).* This is the note's construction (l.123-129).
- Take x ∈ X and an occurrence of a word v of length n−1 at p. Let q be the first occurrence of v at or after p + R_X(n) − n + 1.
- The cyclic word x_{[p,q)} contains every n-word, and its windows across the seam are windows of x_{[p, q+n−1)}.
- Any window of length R_X(n−1) contains v, so q − p ≤ R_X(n) + R_X(n−1) ≤ 2R_X(n).

(d) *N_X(n) ≤ (p_X(n)+1)p_X(n−1).*
- The Rauzy graph Γ has vertices L_{n−1}(X) and an edge v → v' for each n-word with prefix v and suffix v'. Γ is strongly connected by minimality.
- Build a closed walk: repeatedly walk at most V−1 steps to the tail of the next uncovered edge and traverse it; at the end, return to the start.
  Its length is at most E·V + V, with E = p_X(n) and V = p_X(n−1).
- The letters along a closed walk form a cyclic word whose cyclic windows of length n are exactly the traversed edges. ∎

**Corollary A1 (Sturmian upper bound).** If X is Sturmian, then N_X(n) ≤ 2n+2 and `L_X(r) ≤ 2^{9(8r+4)²}`.

*Proof.*
- p_X(n) = n+1, so Γ has V = n vertices and E = n+1 edges, and it is strongly connected.
- An ear decomposition of a strongly connected digraph has E − V ears, so Γ is a cycle C plus one directed ear P.
- Go around C, along P, and back along C: this covers every edge with a walk of length ≤ 2|C| + |P| ≤ 2E = 2n+2.
- Apply Theorem A with n = 4r+1.
- Agrees with `pestov91-four-regular-expanders-and-limits-2026-09-13.md` §5 (b_X(r) = 2r+2). ∎

## 2. Lower bounds valid for every X
**Lemma 1 (units are cheap).** For i ≠ j, a ring element r, and integers a, b: `|e_ij(u^a r u^b)| ≤ |e_ij(r)| + 12(|a|+|b|)`.

*Proof.*
- Let k be the third index and w_{ik}(s) = e_ik(s)e_ki(s^{-1})e_ik(s). Over F_2 its (i,k)-block is [[0,s],[s^{-1},0]].
- So D = w_{ik}(u)w_{ik}(1) = diag(u at i, u^{-1} at k, 1 at j), of length 6. Both factors are involutions, so D^{-1} = w_{ik}(1)w_{ik}(u) also has length 6.
- Conjugation by D maps e_ij(r) = I + rE_ij to I + d_i r d_j^{-1} E_ij = e_ij(ur), and conjugation by D^{-1} gives e_ij(u^{-1}r).
- With D' = diag(u at j, u^{-1} at k), conjugation by D' gives e_ij(ru^{-1}), and by D'^{-1} gives e_ij(ru).
- Each step adds 12 letters. ∎

**Lemma 2 (cylinder transvections).** Let w be a word of length 2^h and [w] = {x : x_{[0,2^h)} = w}.
Then `|e_ij(e_{[w]})| ≤ 25·4^h` for all i ≠ j.

*Proof.*
- h = 0: e_ij(e_a) ∈ S.
- Write w = w'w'' with |w'| = |w''| = 2^h. Then e_{[w]} = e_{[w']} · u^{-2^h} e_{[w'']} u^{2^h}, since u^{-c}e_V u^c = e_{T^{-c}V}.
- So e_ij(e_{[w]}) = [e_ik(e_{[w']}), e_kj(u^{-2^h}e_{[w'']}u^{2^h})], using [e_ik(r), e_kj(s)] = e_ij(rs) (note l.91).
- By Lemma 1, T(h+1) ≤ 2T(h) + 2(T(h) + 24·2^h) = 4T(h) + 48·2^h.
- With T(0) = 1: T(h) ≤ 4^h + 48·4^{h−1}·Σ_{k≥0}2^{-k} = 25·4^h. ∎

**Theorem B.**
- (B1) There is λ > 1 with L_X(r) ≥ |B(r)| ≥ λ^r.
- (B2) For h ≥ 0 and r ≥ 125·4^h, L_X(r) ≥ 60^{p_X(2^h)}. So `L_X(r) ≥ 60^{p_X(⌈√(r/500)⌉)}` for all r ≥ 125.

*Proof of (B1).* φ is injective. G_X is infinite with property (T), so it is non-amenable and has exponential growth.

*Proof of (B2).*
- Let V = L_{2^h}(X) and a_v = e_{[v]}. These are nonzero idempotents with a_v a_w = 0 for v ≠ w.
- Put x^v_ij = e_ij(a_v). By Lemma 2 it lies in B(25·4^h). In G_X:
  - (i) [x^v_ik, x^v_kj] = x^v_ij for distinct i, j, k: a relation of length ≤ 125·4^h;
  - (ii) [x^v_ij, x^w_kl] = 1 for v ≠ w, because a_v a_w = a_w a_v = 0: a relation of length ≤ 100·4^h.
- By Lemma 0, q^v_ij = φ(x^v_ij) satisfy (i) and (ii) in Q.
- P_v = ⟨q^v_ij⟩ is perfect by (i). It is nontrivial, because x^v_12 ≠ 1 and φ is injective.
- By (ii) the P_v commute pairwise, so multiplication μ: ∏_v P_v → Q is a homomorphism.
- If (p_v) ∈ ker μ, then p_v = ∏_{w≠v} p_w^{-1} centralizes P_v, so ker μ ⊆ ∏_v Z(P_v).
- So |Q| ≥ ∏_v |P_v/Z(P_v)|. Each P_v/Z(P_v) is a nontrivial perfect group, since a nontrivial perfect group is non-abelian.
- Every group of order < 60 is solvable, so each factor has order ≥ 60.
- Choosing h maximal with 125·4^h ≤ r gives 2^h ≥ √(r/500), and p_X is nondecreasing. ∎

**Corollary B3 (entropy).** If X has topological entropy η > 0, then p_X(n) ≥ e^{ηn}, so
`L_X(r) ≥ 60^{exp(η√(r/500))}`, a doubly exponential lower bound.
Since N_X(n) ≤ (p_X(n)+1)p_X(n−1), Theorem A gives a doubly exponential upper bound.

## 3. Where the general lower bound loses
(B2) pays 4^h letters for a cylinder of length 2^h. That gives the √r in place of r/C, the same loss as Bradford–Dona's
lower bound exp(c·p_X(n^{1/2})) for [[σ]]' (their Theorem 1.2, per the arXiv HTML).

For linearly recurrent X, the tower argument of part 2 with full cylinders only recovers exp(cr).

Part 2 shows the loss is not intrinsic: for Sturmian X, clopen sets cut out by two letter conditions have large return times
and O(m)-letter transvections, and the true growth is exp(Θ(r²)).
