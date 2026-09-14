# SK review 3, part 2: gap sofic approximations are local embeddings

Lane `sk-verify-3`, 2026-09-13.
Queue item: `gap-sofic-approximations-are-local-embeddings | sk-fp-sofic-a | research/artifacts/sk-fp-sofic-a-proposal-2026-09-13.md` (landed 42196f9cb2).
Main read at tip `4779034a9d`.

## Verdict

| item | verdict |
|---|---|
| claim `gap-sofic-approximations-are-local-embeddings`, route `-proof` | PASS |
| proposal Option B (three sentences, l.63-65) | PASS |
| proposal Option A, first paragraph | GAP in wording, with a repair below |
| proposal Option A, Caprace–Rémy sentence | credit owed a source check (sk-citations) |

The route is self-contained (`requires: []`) and imports nothing. Every step was re-derived.

## 1. The theorem

**Gap ⇒ LEF.**
- The defect x_N = σ_N(gh)⁻¹σ_N(g)σ_N(h) lies in H_N, because H_N is a subgroup containing every value of σ_N.
- Left invariance gives fpr(x_N) = 1 − d(σ_N(g)σ_N(h), σ_N(gh)) → 1. On the finite set of pairs, the gap forces x_N = 1 for large N.
- Injectivity: with a = σ(g), b = σ(h)σ(h⁻¹g), c = σ(h), the triangle inequality d(a,c) ≥ d(b,c) − d(a,b) plus invariance gives d(σ(g),σ(h)) ≥ d(σ(h⁻¹g),1) − o(1) → 1.
- So σ_N|F is an injective partial homomorphism into the finite group H_N.

**LEF ⇒ gap.**
- φ_N(e) = φ_N(e)², so φ_N(e) = 1.
- The left regular action of Q_N has gap 1.
- For g ≠ e, eventually φ_N(g) ≠ φ_N(e) = 1 by injectivity, and a nontrivial left translation moves every point.

PASS.

## 2. The gap families

**(A)** x(y) = aα(y), x ≠ 1.
- A fixed y₀ gives Fix(x) = y₀A^α, since aα(y₀z) = y₀z iff α(z) = z. A left coset of A^α has |A^α| points.
- If A^α = A, then α = 1 and a ≠ 1, so x has no fixed point. Otherwise [A : A^α] ≥ 2 and fpr ≤ 1/2.
- The pairs (a, α) compose as a₁α₁(a₂), α₁α₂ and act faithfully; evaluate at y = e to recover a.

PASS.

**(P)** X ∈ GL_m(F_q) non-scalar, m ≥ 2.
- Fixed lines are the lines of the eigenspaces E_λ. These are independent, with Σd_λ ≤ m and d_λ ≤ m−1.
- f(d) = q^d − 1 is superadditive. The total is at most f(d₁) + f(m − d₁) for the largest part d₁ ∈ [1, m−1] (if there is no eigenvalue, fpr = 0). This is convex in d₁, so it is at most f(m−1) + f(1).
- q = 2: only λ = 1, so fpr ≤ (2^(m−1) − 1)/(2^m − 1) < 1/2.
- q ≥ 3: q^(m−1)(q−2) ≥ q(q−2) and q(q−2) − (2q−3) = (q−1)(q−3) ≥ 0.

PASS.

## 3. Corollaries

- **Corollary 1.** This is "finitely presented LEF ⇒ residually finite".
  - The words have length ≤ r ≥ L, and prefix induction needs w̄′, s, w̄′s ∈ B(r), which holds.
  - φ(s)φ(s⁻¹) = φ(e) = 1, so ψ is defined on the free group, kills the relators, and agrees with φ on B(r).
  - PASS.
- **Corollary 2.**
  - Trivial defects on B(L) × B(L) include (e,e), which gives σ(e) = 1, and (s, s⁻¹).
  - Prefix induction needs only pairs with both entries in B(L), which is what the hypothesis supplies. So ψ_N is a homomorphism.
  - ψ_N is nontrivial, since d(σ_N(s),1) → 1. Simplicity makes it injective, which contradicts finiteness of Sym(Ω_N).
  - The nontrivial defect has fpr → 1 because there are finitely many pairs.
  - PASS. (It also follows at once from the theorem plus Corollary 1; the node's version adds the quantitative statement about the defect.)
- **Corollaries 3–4.** These specialize the result: GL_(3N)(F_2) on F_2^(3N) lies in family (A). The exclusion concerns the natural actions on vectors or lines only, as the node says. PASS.
- **Model tests.** Z, Sym(Ω_N) (a transposition has no gap), BS(2,3) (finitely presented, residually solvable, not RF, hence not LEF), and Thompson's V are all consistent.

**Credit note (recalled, not read at source).** The theorem is an instance of the folklore remark that approximation by finite groups carrying uniformly discrete bi-invariant metrics is the same as LEF. The Hamming metric on Sym(Ω) is bi-invariant, and a gap δ makes it δ-discrete on H_N; compare Thom's ICM 2018 survey "Finitary approximations of groups and their applications". The node already claims no novelty. sk-novelty may want one citation for the remark.

## 4. The proposal text

**Option B** (l.63-65 plus three lines).
- "A finitely presented LEF group is residually finite, so $G_X$ is not finitely presented." This is correct: G_X is infinite and simple, so it is not RF.
- The open-status sentence rests on the lane's bounded check (§1 of the proposal).
- PASS.

**Option A, first paragraph.** GAP (wording).
- "let $B$ be a ball in $G$ that contains all relators" does not parse: relators are words in the free group and represent $e$ in $G$.
- Repair:
  ```latex
  Let $G=\langle S\mid R\rangle$ be finitely presented and LEF, and let $B$ be
  the ball in $G$ whose radius is the length of the longest relator. A local
  embedding of $B$ into a finite group extends to a homomorphism of $G$ that is
  injective on $B$, so $G$ is residually finite.
  ```
  The extension step is Corollary 1's prefix induction.
- With this repair the paragraph is correct.

**Option A, second paragraph.** "Two distinct affine maps of a finite vector space differ on at least half of its vectors." This is family (A): d(x,y) = 1 − fpr(y⁻¹x) ≥ 1/2. The rest of the paragraph follows from §1. PASS.

**Option A, Caprace–Rémy sentence.** Not verified by me. One citation is asked to carry finite presentation, simplicity and property (T) of Kac–Moody lattices.
- Caprace–Rémy (Invent. Math. 176, 2009) prove simplicity.
- Finite presentation and (T) for these lattices usually carry other attributions (e.g. Abramenko–Mühlherr for 2-spherical presentations, Dymara–Januszkiewicz for (T); recalled, not read).
- sk-citations should confirm the page of Caprace–Rémy that states the combination before this sentence is used.

## 5. Queue item 2: `tower-subshift-elementary-group-is-el-3k-of-base` (sk-open-5)

Main read at tip `f09fc92674`. Route `-proof`, `requires: []`. Verdict: **PASS** for items 1–3. Every step re-derived.

**Item 1: the tower is a minimal subshift.**
- S^k acts on X×{0} as T. For 0 ≤ i < k, S^i maps level 0 onto level i without wrap-around. So every S-orbit is dense in every level, and S is minimal.
- Coding S^n(x,i) = (T^⌊(i+n)/k⌋ x, (i+n) mod k) by the letter (x_⌊(i+n)/k⌋, (i+n) mod k) is continuous and equivariant.
- It is injective: i is read at time 0, and x_j is read at any n with ⌊(i+n)/k⌋ = j.
- PASS.

**Item 2: R_(X^(k)) ≅ M_k(R_X).**
- Matrix units: for 0 ≤ i,j ≤ k−1, S^(i−j) carries level j onto level i with no wrap. So u^(i−j) p_j u^(j−i) = p_i, and v_ij = p_i u^(i−j) = u^(i−j) p_j.
  - v_ij v_jl = v_il;
  - v_ij v_j′l = u^(i−j) p_j p_j′ u^(j′−l) = 0 for j ≠ j′;
  - Σ v_ii = 1.
- Corner:
  - p_0 f u^n p_0 = f p_0 e_(S^n(level 0)) u^n vanishes unless k | n.
  - w = u^k p_0 has inverse u^(−k) p_0 in the corner, and w (f p_0) w^(−1) = (f∘S^(−k)) p_0 = (f∘T^(−1)) p_0, because S^k(x,0) = (Tx,0).
  - The algebraic crossed product is the universal unital ring on LC(X) and a unit u with u f u^(−1) = f∘T^(−1). So f ↦ f p_0, u ↦ w defines a unital homomorphism.
  - It is onto, since w^m = u^(km) p_0.
  - It is injective, since powers of u are independent over LC(X^(k)).
- PASS.

**Item 3: EL_n(M_k(R)) = EL_(nk)(R) for n ≥ 2.**
- (⊆) The factors I + A_ab E_((i,a),(j,b)) have pairwise products of off-diagonal parts equal to 0, since (j,b) ≠ (i,a′) when j ≠ i.
- (⊇) Take ρ = rE_ab and σ = E_bb, with a ≠ b and q′ ≠ p.
  - ρσ = rE_ab, σρ = 0 and ρσρ = 0.
  - So XY = (I + ρσE_pp)YX, where the extra terms σσE_pp E_q′p and ρσρE_pp E_pq′ vanish.
  - Hence [X,Y] = I + rE_ab E_pp.
- PASS.

**Assembly.** M_3(M_k(R_X)) = M_(3k)(R_X), and ring isomorphisms carry elementary matrices to elementary matrices. Group isomorphisms carry centres onto centres. PASS.

**Outside the review.** The period-doubling consequence (X^(2) ≅ X, so EL_3(R_X) ≅ EL_6(R_X)) rests on `period-doubling-subshift-algebra-is-its-own-matrix-ring`, which is not a `requires` of this route. I did not review it here.

**Credit note (recalled, not read at source).** Both identities are standard in spirit.
- The crossed product of a height-k Kakutani tower is M_k of the base crossed product (the C*-analogue is folklore through induced systems).
- EL_n(M_k(R)) = EL_(nk)(R) for n ≥ 2 is a textbook K-theory identity.
The node claims no novelty. What it adds for the note: any rigidity statement for G_X ≅ G_Y must allow G_(X^(k)) ≅ EL_(3k)(R_X).
