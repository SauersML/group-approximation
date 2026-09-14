# sk-review-1, part 2: the LEF recurrence bound and sk-lef-short's finite-models section

- Reviewer: lane sk-referee-1, a Claude Code agent. This is not a human review.
- Base: frozen note md5 7b3dc4ec92b4581553bc0dc2b0edcb99. Main tip at review: 0efb32a5a0.
- Every step was re-derived by hand, with the note's conventions: (Tx)_n = x_{n+1}, u f u^{-1} = f∘T^{-1}, Pδ_n = δ_{n+1}, D_k(f)δ_n = f(T^ny_k)δ_n.

## 1. `subshift-lef-models-period-below-twice-recurrence` + `-proof` (sk-lef-short): PASS
**Item 1 (periodic models, p_X(2k+1) ≤ N_k ≤ 2Rec_X(2k+1) - 4k).**
- Rec_X(2k) ≤ m = Rec_X(2k+1), because every word of X of length 2k extends to one of length 2k+1.
- x_{[m-2k,2m-2k)} is a word of X of length m, so it contains v = x_{[0,2k)} at some N ∈ [m-2k, 2m-4k]. For k = 0, v is empty and N = m.
- x_{[N,N+2k)} = v gives x_i = x_{i-N} on [N,N+2k). So the N-periodic y with y_{[0,N)} = x_{[0,N)} agrees with x on [0,N+2k).
- A window of y of length 2k+1, after translation by a multiple of N, starts in [0,N) and ends by N+2k-1. So it lies in x_{[0,N+2k)}.
- Conversely, N+2k ≥ m, so x_{[0,N+2k)} contains x_{[0,m)}, which contains every word of L_{2k+1}(X).
- An N-periodic sequence has at most N windows of each length, so N ≥ p_X(2k+1) ≥ 2k+2 (Morse–Hedlund for infinite X). Also N ≤ 2m-4k < 2m.

**Item 2 (ball dictionary).**
- (g·e_ij(λs))_{pq} = g_pq + δ_{qj}g_{pi}λs.
- (fu^j)u^{±1} = fu^{j±1}, and (fu^j)e_a = f·(e_a∘T^{-j})u^j, where e_a∘T^{-j} = [x_{-j} = a]. The new coordinate -j already lies in [-t,t], so the window bound "one more coordinate" is conservative. By induction on right multiplication, the entries of every g ∈ B(r) lie in V_r. The ball is symmetric, so the same holds for g^{-1}, and V_r is a span, so it holds for g - h.
- With k = 2r:
  - φ is well defined and F_q-linear on V_{2r}, because the windows of y_k of length 4r+1 are words of X.
  - For a = fu^i and b = gu^j in V_r, ab = f(g∘T^{-i})u^{i+j} ∈ V_{2r}, and P^iD_k(g)P^{-i} = D_k(g∘T^{-i}). So φ(ab) = φ(a)φ(b).
  - Entrywise this gives φ(gh) = φ(g)φ(h) for ALL g,h ∈ B(r), which is stronger than products staying in B(r). In particular φ(g)φ(g^{-1}) = I.
- Injectivity: take a nonzero coefficient f_j (|j| ≤ r) of an entry of g - h. Its [-r,r]-window word lies in a word of L_{4r+1}(X) = L_{4r+1}(y_k), so D_k(f_j) ≠ 0. Distinct exponents occupy disjoint entries, since N_k ≥ 4r+2 > 2r.
- Bound: |GL_{3N}(F_q)| < q^{9N²} and N < 2Rec_X(4r+1), so F(r) < q^{36Rec_X(4r+1)²}.

**Item 3.** Substitution, with Durand's linear recurrence recalled only for the example.

**Notes.**
- N1. The recalled inputs are Morse–Hedlund p_X(n) ≥ n+1, used for N_k > 2r in the injectivity step, and Durand, used for the example. Both are standard.
- N2. The claim body says "**ESTABLISHED (unreviewed).**" The owner may now cite this review.

## 2. sk-lef-short Replacement B (the recommended finite-models section, 26 lines): PASS
Sentence by sentence:
- "By minimality every word of X occurs in x, and x_{[0,2k)} recurs at arbitrarily large positions." Every forward orbit of a minimal system is dense. ✓
- "Choose such a position N_k with all words of length 2k+1 of X occurring in x_{[0,N_k+2k)}." All words occur at nonnegative positions, so a large recurrence works. ✓
- "This word begins and ends with x_{[0,2k)}, so it has period N_k, and the N_k-periodic sequence y_k ... has the same words of length 2k+1 as X." ✓ by the window argument of §1.
- "N_k is at least the number of these words, which tends to infinity because X is infinite." ✓
- D_k(f) is well defined, because (T^ny_k)_{[-k,k]} = y_{[n-k,n+k]} ∈ L(X), and it depends only on n mod N_k. ✓
- PD_k(f)P^{-1} = D_k(f∘T^{-1}) once f∘T^{-1} depends on [-k,k]. So the additivity and multiplicativity identities hold for each fixed pair r, s once k is large. ✓
- Separation: N_k → ∞, so the exponents of r are eventually below N_k/2, where the P^j have disjoint supports. ✓
- Entrywise map on a finite F: finitely many identities are needed (products gh ∈ F, the products giving φ_k(g)φ_k(g^{-1}) = I, and sums) and finitely many nonvanishings (entries of g-h), and all hold for large k. So the map is injective, lands in GL_{3N_k}(F_2), and preserves products staying in F. ✓

**Optional notes on the text.**
- B1. "has the same words of length $2k+1$ as $X$" compresses both inclusions. The clause "because each of its windows lies in $x_{[0,N_k+2k)}$" names the one the reader checks. +0 or +1 line.
- B2. φ_k(r) is defined only once k exceeds the windows of r's coefficients. "for all $r,s\in R$ ... hold for large $k$" implicitly includes that. Optional: "(both sides are defined for large $k$)".
- B3. The last sentence repeats "so": "So $G$ is LEF, and so it is sofic and hyperlinear". Suggest "So $G$ is LEF, and it is sofic and hyperlinear~\cite{Pestov}."
- B4. B supersedes sk-referee-1 proposals P1 (the segment w), P2 (the formula for D) and P11 (inverse products), and the "allowed window" point U9.

## 3. Replacement A, §6a, §6b, §6c: PASS
- **A.**
  - M_3(∏_ω M_{N_k}(F_2)) = ∏_ω M_{3N_k}(F_2).
  - A unit of an algebraic ultraproduct is a unit in ω-almost every coordinate.
  - The coordinate identities hold for all large k, so φ is a unital injective ring homomorphism.
  - LEF of G follows by Łoś for finitely many identities and inequalities.
- **§6a.** The first position N ≥ m-2k with x_{[N,N+2k)} = x_{[0,2k)} lies in [m-2k, 2m-4k], so N_k < 2m. And x_{[0,N_k+2k)} ⊇ x_{[0,m)}. ✓
- **§6b.** SL_{3N}(F_2) = GL_{3N}(F_2) is simple for 3N ≥ 3, so with A, G is a subgroup of an ultraproduct of finite simple groups. ✓
- **§6c** (the minimal repair of the current text): ✓.

## 4. For revision 1
- The finite-models section (B) is independent of the simplicity section: sk-simplicity-short-a's text never uses φ_k.
- B still uses minimality, and the covering step of sk-proof-minimal-concrete (part 1 of this review) also uses minimality.
