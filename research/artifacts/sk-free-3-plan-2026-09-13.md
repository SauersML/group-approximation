# sk-free-3 plan: the conjugacy problem of G_X (2026-09-13)

Lane sk-free-3 (wave 10, free lane; logic and computability). Main tip at planning time: 3341ad6094.

## Choice
The note's §3 shows WP(G_X) ≡_T L(X), so every Turing degree occurs as a word-problem degree (node `subshift-elementary-group-word-problem-degree`). The conjugacy problem was explicitly not pursued (sk-word-problem proposal, sk-panel-referee-5 §2 item 4).

This lane proves that the conjugacy problem sees the dimension group, and that it can be strictly harder than the word problem.

**Target theorem (CP).** For every Turing degree d there is an infinite minimal subshift X such that the word problem of G_X has degree d and the conjugacy problem of G_X has degree d′. In particular some G_X has solvable word problem and unsolvable conjugacy problem.

Why this and not the alternatives:
- **First-order rigidity / bi-interpretability of G_X with (N,+,·,L(X)).** R_X does interpret arithmetic with parameters: C_R(u) = F_2[u^{±1}] by minimality, and its units are the powers of u. But the G ↔ R bi-interpretation needs definable matrix entries without bounded elementary generation. That is a real obstacle, so it stays a secondary target (§5).
- **The isomorphism problem** depends on isomorphism rigidity, which is owned by the live sk-iso-rigidity lane.
- **CP** is concrete. It uses only the note's finite models plus Kakutani–Rokhlin towers, and it lands in §3 at the cost of about 4 lines.

## 1. Lemma K (transvection conjugacy = topological full group equivalence)
Let X be an infinite minimal subshift, R = LC(X,F_2)⋊Z and G = EL_3(R). For clopen A, B ⊆ X the following are equivalent:
- (a) e_13(1_A) and e_13(1_B) are conjugate in G;
- (b) 1_A − 1_B = g∘T − g for some g ∈ C(X,Z);
- (c) γ(A) = B for some γ in the topological full group [[T]].

**(c) ⇒ (a).** γ gives the unit w = Σ_levels 1_{T^{σ(j)}Z} u^{σ(j)−j} of R with w 1_A w^{−1} = 1_B. In characteristic 2, e_12(c)e_21(c^{−1})e_12(c)·w(1) = diag(c,c^{−1},1), so diag(w,w^{−1},1) and diag(1,w^{−1},w) lie in G. Their product k = diag(w,w^{−2},w) satisfies k e_13(r) k^{−1} = e_13(w r w^{−1}).

**(b) ⇒ (c).** Kakutani–Rokhlin towers:
- Choose a nonempty clopen Z on which g is constant.
- Take the first-return tower partition over Z, refined so that every level lies inside A or its complement, and likewise for B.
- On a tower of height h with base point z, Σ_{j<h} f(T^j z) = g(T^h z) − g(z) = 0, since T^h z and z both lie in Z. So each tower has equally many A-levels and B-levels.
- Match A-levels to B-levels, and complements to complements, by level shifts. This defines γ ∈ [[T]] with γA = B.

**(a) ⇒ (b), route 1: finite models and a Livšic loop argument.**
- Let k conjugate the two transvections, and f = 1_A − 1_B of radius r.
- Take L large compared with r and with the degrees of the entries of k^{±1}. Let x[i,j) be a return loop of an L-window (x[i,i+L) = x[j,j+L)).
- The periodic word (x[i,j))^∞ has all windows of length ≤ L+1 in L(X). The note's model φ: fu^a ↦ D(f)P^a is then multiplicative on the finitely many entries involved. Only inclusion of languages is needed, not equality.
- So I + E_13 D(1_A) and I + E_13 D(1_B) are conjugate in SL_{3N}(F_2). Their ranks agree, which says the loop sum Σ_{t∈Z/N} f(window at t) vanishes.
- Vanishing loop sums make S_k = Σ_{i<k} f(T^i x) a function of the L-window at k−r. Along a dense forward orbit this defines g ∈ C(X,Z) with g∘T − g = f.

**(a) ⇒ (b), route 2 (cross-check).** A conjugacy gives e_A R ≅ e_B R as right modules, so [1_A] = [1_B] in K_0(R). The node `subshift-crossed-product-k0-is-coinvariant-group` (PASS at group level) identifies K_0(R) with C(X,Z)/(1−T_*), which gives (b).

## 2. Upper bound
CP(G_X) is Σ^0_1 relative to WP(G_X) ≡_T L(X): search for a conjugator word and check the relation. So CP(G_X) ≤_T L(X)′.

## 3. Construction (recursive language, Σ^0_1-complete coboundary problem)
Directive sequence of constant-length morphisms τ_m: Σ_{m+1} → Σ_m^+ over growing alphabets, with Σ_0 = {s,t,w}.
- **Letters:** Σ_m = {s,t,w} ∪ {x^e, y^e : e < m and machine e has not halted within m steps}.
- **Images:** τ_m(c) = s^k · payload(c) · W_m · t, where:
  - W_m lists every letter of Σ_m once, starts with w, and has no two adjacent s;
  - payloads have one common length π_m, contain no s, and are pairwise distinct;
  - payload(x^e_{m+1}) = x^e_m w^{π−1} and payload(y^e_{m+1}) = y^e_m w^{π−1} while e is running;
  - new pairs x^e, y^e enter at level n_e = e+1 with distinct w/t payloads.
- **Recognizability, by induction on m:** level-(m+1) boundaries are exactly the starts of maximal runs of k level-m s-blocks; letters are decoded by injectivity of τ_m.
- **Minimality:** W_m contains every letter. **Aperiodicity:** constant block length L_m with boundaries detected locally forces L_m | p for every period p. **Recursive L(X):** read the language off level-(m+2) blocks.
- **Pairs:** A_e (B_e) = points where a level-n_e block of letter x^e (y^e) starts at 0. These are clopen.
- **Counts:** d_m(c) = #x^e − #y^e level-n_e sub-blocks in the level-m block of c. While e runs, d_m(x^e) = 1, d_m(y^e) = −1, d_m(others) = 0, and d(W_m) = 0.
- **Halting at step h:** from level h+1 on, x^e and y^e leave the payloads, so d ≡ 0 on all later blocks. g, the within-block count, is continuous, so f_e is a coboundary.
- **Not halting:** all level-(m+1) blocks start with s^k and end with t (proper), so g is constant at level-(m+1) boundaries once L_m > r. Then every level-(m+1) block would have zero sum, but d_{m+1}(x^e) = 1. So f_e is not a coboundary.

With Lemma K, e ↦ (e_13(1_{A_e}), e_13(1_{B_e})) many-one reduces the halting set to CP(G_X). Relativize to an oracle S (running e with oracle S), and encode S into the marker lengths k_m (L(X) recovers the directive sequence level by level). Then WP(G_X) ≡_T S and CP(G_X) ≡_T S′.

## 4. Deliverables and landing plan
- **Artifact** `research/artifacts/sk-free-3-conjugacy-problem-2026-09-13[-partK].md`: full proofs of Lemma K (both routes), the construction, and the degree theorem.
- **Nodes (after grep):**
  - `subshift-el-transvection-conjugacy-is-full-group-equivalence` (+ `-proof`);
  - `subshift-elementary-group-conjugacy-degree-is-jump` (+ `-proof`): for every degree d, some G_X has WP in d and CP in d′;
  - wired to `subshift-elementary-group-word-problem-degree` and `subshift-crossed-product-k0-is-coinvariant-group`.
- **Queue:** both claims in `$SK/queue/sk-verify-13.txt`.
- **Proposal** `research/artifacts/sk-free-3-proposal-2026-09-13.md`: a ≤ 5-line addition to §3 with verbatim LaTeX.
- **Novelty check (bounded):** f.g. simple or Kazhdan groups with solvable WP and unsolvable CP; computability of dimension groups and coboundaries of computable minimal subshifts.

## 5. Secondary target (only if time remains)
**Model theory of G_X.**
- (i) Th(G_X) is hereditarily undecidable for every X. G_X interprets R_X with parameters: U_13 = C_G({e_12(s), e_23(s) : s ∈ S ∪ {1}}) for a generating set S. R_X interprets F_2[u^{±1}] = C_R(u), and that ring interprets arithmetic.
- (ii) R_X is bi-interpretable with (N,+,·,L(X)) with parameters. With radius bound w, an element r is characterized by p r u^{−i} p = p g_i for all small p.
- (iii) Is G_X first-order rigid among f.g. groups? The obstacle is definable matrix entries without bounded generation.
