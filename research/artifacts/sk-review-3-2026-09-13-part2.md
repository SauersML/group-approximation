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
