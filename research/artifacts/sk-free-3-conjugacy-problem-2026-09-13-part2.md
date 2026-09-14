# sk-free-3: the conjugacy problem of G_X, part 2 — the construction and the degree theorem (2026-09-13)

Part 1 proves Lemma K (transvection conjugacy ⟺ coboundary ⟺ [[T]]-equivalence) and Lemma U (CP(G_X) ≤_T L(X)′).

## 1. Theorem
**Theorem CP.** For every set S ⊆ N there is an infinite minimal subshift X ⊆ {s,t,w}^Z such that WP(G_X) ≡_T S and CP(G_X) ≡_T S′.

In particular, for S computable, G_X is an infinite finitely generated simple Kazhdan LEF group (the note's Theorem 1) with solvable word problem and unsolvable conjugacy problem, of degree 0′.

## 2. Construction
Fix an enumeration M_e of oracle Turing machines, and let H(e,m) mean "M_e^S halts within m steps". H is computable from S, uniformly.

**Alphabets.** Σ_0 = {s,t,w}. For m ≥ 1:
- E_m = {e < m : ¬H(e, m−1)};
- Σ_m = {s,t,w} ∪ {x_e, y_e : e ∈ E_m}.

So E_{m+1} ⊆ E_m ∪ {m}. The pair x_m, y_m enters at level m+1 unless H(m,m). A pair retires at level m+1 once H(e,m) holds.

**Morphisms.** For m ≥ 0 and c ∈ Σ_{m+1}, define τ_m(c) = s^{k_m} · π_m(c) · W_m · t ∈ Σ_m^+, where:
- **Marker:** k_m = 2 + S(m).
- **W_m:** the word listing every letter of Σ_m exactly once, starting with w s t, then x_e, y_e for e ∈ E_m in increasing order. It contains exactly one s, between w and t.
- **Payloads π_m:** words of one common length p_m ≥ 5, containing no s, pairwise distinct:
  - continuing carriers (e ∈ E_{m+1} ∩ E_m): π_m(x_e) = x_e w^{p_m−1} and π_m(y_e) = y_e w^{p_m−1};
  - fixed letters: π_m(s) = w^{p_m}, π_m(t) = t w^{p_m−1}, π_m(w) = w t w^{p_m−2};
  - entering pair (m ∈ E_{m+1}): π_m(x_m) = w w t w^{p_m−3} and π_m(y_m) = w w w t w^{p_m−4}.

  The fixed and entering payloads are words over {w,t}. The carrier payloads start with distinct carrier letters, so π_m is injective.
- **Lengths:** |τ_m(c)| = ℓ_m := k_m + p_m + |Σ_m| + 1 for every c.

**Blocks and subshift.**
- B_0(c) = c, and B_{m+1}(c) = B_m(τ_m(c)), the concatenation of the level-m blocks of the letters of τ_m(c).
- Every level-m block has length L_m = Π_{j<m} ℓ_j.
- X is the set of x ∈ Σ_0^Z all of whose finite subwords occur in some B_m(c).

## 3. Properties

**(P0) Every point has a level-m decomposition.** Each x ∈ X can be written as x = ⋯B_m(c_{−1})B_m(c_0)B_m(c_1)⋯, with boundaries φ + L_mZ and a letter sequence (c_j) ∈ Σ_m^Z every finite subword of which occurs inside some τ_m⋯τ_{M−1}(c″).
- Each window of x lies in some B_M(c), and B_M(c) is a concatenation of level-m blocks.
- Take a sequence of windows exhausting x and extract, by compactness, a phase modulo L_m and letters.

**Nonemptiness.** B_{M+2}(s) contains B_{M+1}(s) with a full level-(M+1) block on each side: it contains the marker B_{M+1}(s)^{k} with k ≥ 2 after B_{M+1}(t) from W. So the blocks extend on both sides, and X ≠ ∅.

**(P1) Recognizability, by induction on m.** Given the level-m letters of x, the level-(m+1) boundaries are exactly the starts of maximal runs of at least two letters s, i.e. the positions j with c_{j−1} ≠ s = c_j = c_{j+1}.
- In a concatenation of images τ_m(c′), a letter s occurs only in the markers s^{k_m} (k_m ≥ 2) and once inside W_m, where its neighbours are w and t.
- π_m contains no s, a marker is preceded by t (the last letter of the previous image) and followed by a payload letter ≠ s.
- So runs of ≥ 2 letters s are exactly the markers.

The level-(m+1) letters are then read off by injectivity of τ_m. So there is r_{m+1} such that the level-(m+1) boundaries and letters at a position are functions of the window of radius r_{m+1}. In particular the decomposition in (P0) is unique.

**(P2) Minimality.** W_m lists every letter of Σ_m, so every B_{m+1}(c) contains every B_m(c′).
- A word v of X occurs in some B_M(c), hence in every B_{M+1}(c″).
- Every x ∈ X contains some B_{M+1}(c″) by (P0), so it contains v. Hence X is minimal.

**Aperiodicity.** If T^p x = x, the level-m boundary set φ + L_mZ of x is invariant under translation by p, because it is locally determined (P1). So L_m | p for all m. Since L_m → ∞, p = 0. So X is infinite.

**(P3) L(X) ≤_T S.** Let λ = |v| and choose m with L_m ≥ λ.
- A word of X of length λ lies inside two consecutive level-m blocks, which lie inside one B_{m+1}(c) or straddle a level-(m+1) boundary.
- In the second case the pair is B_m(t)B_m(s). B_{m+2}(s) contains W_{m+1} = w s t …, so it contains B_{m+1}(w)B_{m+1}(s) and with it that boundary pair; it also contains every B_{m+1}(c).
- So L_λ(X) is the set of subwords of length λ of B_{m+2}(s), which S computes.

**(P4) S ≤_T L(X).** By induction L(X) computes Σ_m, B_m and r_m.
- **The bit S(m).** k_m = 3 iff some word of L(X) of length 2r_m + 10L_m decodes, in its interior, to the letter pattern t s s s. When k_m = 2 the letter sequences never contain sss.
- **Σ_{m+1}.** The carrier letters existing at level m+1 are read the same way, from the payload patterns s^{k_m}x_e w and s^{k_m}w w t w.

This gives B_{m+1} and r_{m+1}.

**(P5) The pairs.** Let A_e (respectively B_e) be the set of x ∈ X such that a level-(e+1) block with letter x_e (respectively y_e) starts at position 0. By (P1) these are clopen, and a list of cylinders for them is computable from S. If H(e,e), then A_e = B_e = ∅.

Let f_e = 1_{A_e} − 1_{B_e}. For m ≥ e+1 and c ∈ Σ_m, let d_m(c) be the number of level-(e+1) sub-blocks with letter x_e in B_m(c), minus the number with letter y_e.

**Claim.** While e ∈ E_m: d_m(x_e) = 1, d_m(y_e) = −1, d_m(c) = 0 for all other c, and d_m(W_m) = 0. Once e ∉ E_{m+1} (retirement), d_{m′} ≡ 0 for all m′ ≥ m+1.
- **Base m = e+1:** by definition.
- **Step with e ∈ E_{m+1}.** d_{m+1}(c) = d_m(π_m(c)) + d_m(W_m), because s, t and w have d_m = 0. The payload of x_e contains x_e once; the payload of y_e contains y_e once; every other payload contains neither. W_{m+1} contains x_e and y_e once each, so d_{m+1}(W_{m+1}) = 0.
- **Retirement step.** No payload at level m+1 contains x_e or y_e, so d_{m+1}(c) = d_m(W_m) = 0. Blocks at higher levels are sums of zeros.

**(P6) M_e^S halts ⇒ f_e is a coboundary.** Let m+1 be the retirement level.
- Let g(x) be the count, over positions [b,0), of x_e-block starts minus y_e-block starts, where b ≤ 0 is the start of the level-(m+1) block containing 0. By (P1), g ∈ C(X,Z).
- If position 1 is not a level-(m+1) boundary, g(Tx) = g(x) + f_e(x).
- If it is a boundary, g(Tx) = 0 and g(x) + f_e(x) = d_{m+1}(c) = 0.
- So f_e = g∘T − g, using the convention (Tx)_i = x_{i+1}.

**(P7) M_e^S never halts ⇒ f_e is not a coboundary.**
- Suppose f_e = g∘T − g with g a function of x[−r,r]. Choose m ≥ e+1 with L_m > r.
- At a level-(m+1) boundary i, the window x[i−r, i+r] is the last r letters of B_m(t) followed by the first r+1 letters of B_m(s); it does not depend on i. So g(T^ix) is the same at all such boundaries.
- Hence over a level-(m+1) block [i, i+L_{m+1}) with letter c, Σ_j f_e(T^jx) = g(T^{i+L_{m+1}}x) − g(T^ix) = 0.
- But this sum is d_{m+1}(c), and c = x_e ∈ Σ_{m+1} occurs in x (by P2) with d_{m+1}(x_e) = 1. Contradiction.

## 4. Proof of Theorem CP
- **Word problem.** By the note's §3 corollary, WP(G_X) ≡_T L(X). By (P3) and (P4), L(X) ≡_T S.
- **Reduction.** By Lemma K with (P5)–(P7), e ∈ S′ iff e_13(1_{A_e}) and e_13(1_{B_e}) are conjugate in G_X.
  - Words for these elements are computable from S ≤_T WP ≤_T CP (part 1 §3).
  - So S′ ≤_T CP(G_X).
- **Upper bound.** Lemma U gives CP(G_X) ≤_T L(X)′ ≡_T S′.

## 5. Scope and firewalls
- **Where this sits.** The construction is one explicit S-adic family. Most Sturmian subshifts with computable slope give a decidable coboundary problem on cylinders (K^0 = Z + αZ). So "CP ≡ L(X)′ for every X" is FALSE as a general claim and must never be stated.
- **What is and isn't claimed.** Only root transvections enter the lower bound. The full conjugacy problem of G_X is bounded above by L(X)′ and is otherwise not analyzed.
- **Novelty (bounded; two web searches, 2026-09-13).**
  - A finitely generated branch group with solvable word problem and unsolvable conjugacy problem answers a question of Bartholdi–Grigorchuk–Šunić: arXiv:2509.12161, IMRN 2026.
  - Automaton groups with unsolvable conjugacy problem exist: Šunić–Ventura, arXiv:1010.1993.
  - No simple or Kazhdan example turned up. Novelty checks at source are left to a verifier.
