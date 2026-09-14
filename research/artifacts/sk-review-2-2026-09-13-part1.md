# sk-review-2, part 1: verdicts on the queue of sk-referee-2 (2026-09-13)

Verifier: sk-referee-2. Queue `sk/queue/sk-referee-2.txt`, entries 1-5 as of 18:58. Nodes were read at main's tip
(d9f33469df) with `git show`. Line numbers of the note refer to `manuscript-disk-1646.tex`.

Verdict key:
- PASS: the statement and its route are correct as written.
- PASS+repair: the mathematics is correct, and a wording or bibliographic repair is listed.
- GAP: the route does not support the statement as written; a repair is listed.
- FAIL: the statement is false or unsupported.

## Summary
| # | id | owner | verdict |
|---|---|---|---|
| 1 | `simple-kazhdan-group-lacks-factorization-property` (+ `-proof`) | sk-questions-oa | PASS+repair |
| 1b | `kirchberg-property-t-fp-implies-rf` | sk-questions-oa | GAP (scope: "iff" vs the verified direction) |
| 1c | `kirchberg-property-t-fp-implies-rf-citation` | sk-questions-oa | GAP (bibliographic: issue and pages) |
| 2 | `simple-kazhdan-group-gives-property-t-factor-in-r-omega` (+ `-proof`) | sk-questions-oa | PASS+repair |
| 2b | `infinite-simple-groups-are-icc` (+ `-proof`) | sk-questions-oa | PASS |
| 3 | `continued-fraction-real-realizes-every-turing-degree` (+ `-proof`) | sk-word-problem | PASS |
| 4 | route `every-turing-degree-simple-kazhdan-lef-via-continued-fractions` | sk-word-problem | PASS |
| 4b | Proposal A LaTeX for l.229-262 | sk-word-problem | PASS+repair |
| 5 | `full-group-word-problem-iff-recursive-language` (+ `-citation`) | sk-novelty | PASS |

## 1. The factorization property
**Claim.** For G_X = EL_3(LC(X,F_2)⋊Z), G_X does not have Kirchberg's factorization property.

**Checks.**
- Not residually finite. A finite quotient of a simple group is trivial or injective, and G_X is infinite. TRUE.
- (T) + factorization property ⇒ residually finite. This is Kirchberg, Math. Ann. 299 (1994). Crossref for
  doi:10.1007/BF01459798 returns: title "Discrete groups with Kazhdan's propertyT and factorization property are
  residually finite", Mathematische Annalen, volume 299, issue 1, pages 551-563, author Kirchberg. So the DOI is
  CONFIRMED.
- A published statement of the conclusion already exists. Main already holds the reviewed import
  `ozawa-kazhdan-liftable-traces-are-fd-limits` (verbatim, arXiv v2 p. 26): "infinite simple groups with Kazhdan's
  property (T) … do not have the property (F) as it was shown by Kirchberg [Ki3]". So the claim is a direct instance
  of a remark in the Ozawa paper the note cites for the question.
- Conclusion: the statement is TRUE and the route is valid.

**Repairs.**
- (1.i) The title says "strictly beyond residual amenability", and the route never proves it. The fact is true, with
  a one-line proof: a nontrivial homomorphism from an infinite simple group to an amenable group is injective, so a
  residually amenable G_X would be amenable, while an infinite (T) group is not. Add this line to the route, or drop
  the phrase.
- (1.ii) Credit. Add Ozawa arXiv v2 p. 26, through `ozawa-kazhdan-liftable-traces-are-fd-limits`, next to Kirchberg.
  The body's sentence "the new element here is simplicity" should say that Ozawa already records the consequence for
  every infinite simple (T) group. G_X supplies the first example that is also sofic.

**1b `kirchberg-property-t-fp-implies-rf`: GAP (scope).**
- The claim says "a property (T) group has the factorization property iff it is residually finite".
- The citation route verifies only the title, which is one direction: (T) + factorization property ⇒ residually
  finite.
- The converse (residually finite ⇒ factorization property) is standard but is not quoted here.
- Every consumer on main uses only ⇒, including the proof route above and `thom-sofic-kazhdan-groups-without-factorization-property`.
- Repair: restate the claim as the verified direction, or add a verbatim source for the converse.

**1c `-citation`: GAP (bibliographic).**
- The node says "no. 3, 551--564" and "DOI NOT yet confirmed".
- Crossref: issue 1, pages 551-563, DOI confirmed. The reviewed Ozawa node also prints 551-563.
- Repair: write issue 1 and pages 551-563, and mark the DOI confirmed.
- The same fix applies to the proposed bibitem in `sk-questions-oa-proposal-2026-09-13.md`, which says 551--564.

**The note sentence (Finding 1).**
- Mathematically correct.
- Calibration for main: it restates Ozawa's own p. 26 remark, so it adds a placement, not a result.
- With the page fix, it is safe to include if the user wants it.

**Status.** No node needs demotion. The owner should apply 1.i, 1.ii, 1b and 1c.

## 2. The property (T) factor in R^ω
**Claim.** L(G_X) is a separable II_1 factor with property (T) that embeds in R^ω.

**Checks.**
- ICC. See 2b. TRUE.
- ICC + (T) ⇒ L(G) is a property (T) factor. Connes–Jones, Bull. LMS 17 (1985) 57-62. This is standard; I did not
  re-read the source.
- Hyperlinear ⇒ L(G) ⊆ R^ω. Ozawa, About the QWEP conjecture, Prop. 7.1. Earlier repo work checked it from the PDF
  (Pestov 9.1 priority audit). TRUE.
- Conclusion: the displayed statement is TRUE.

**Repair (2.i), in the Brown paragraph of the claim and the last sentence of `-proof`.**
- Current wording: "R^ω is McDuff and trivially R^ω-embeddable".
- The problem: R^ω is not separable, while "McDuff factor" and "R^ω-embeddable" are normally defined for separable
  II_1 factors, and Brown's question concerns those.
- Use M = L(G_X) ⊗̄ R instead:
  - M is separable and McDuff (M ≅ M ⊗̄ R);
  - M is R^ω-embeddable: x ⊗ y ↦ (x_n ⊗ y)_n embeds R^ω ⊗̄ R trace-preservingly in (R ⊗̄ R)^ω ≅ R^ω, so
    L(G_X) ⊗̄ R ⊆ R^ω;
  - G_X ⊆ U(L(G_X)) ⊆ U(M).
- This is the reading under which the note's l.38-41 ("Brown asked this in its von Neumann algebra form") matches
  hyperlinearity.

**The note (Finding 2).** I agree with the owner's default: do not add. The hyperlinear clause already answers Brown.

## 2b. `infinite-simple-groups-are-icc`
- The centre is trivial: an abelian simple group is cyclic of prime order, hence finite.
- A finite conjugacy class gives a centralizer of finite index. Its normal core is a finite intersection of
  finite-index subgroups, so it is normal of finite index, and it must be G.
- So g is central, and g = e. PASS.

## 3. `continued-fraction-real-realizes-every-turing-degree`
**Claim.** α_S = [0; 1+χ_S(0), 1+χ_S(1), …] is irrational, lies in (0,1), and α_S ≡_T S.

**Checks.**
- Irrational and in (0,1). An infinite simple continued fraction with positive partial quotients is irrational.
  Also α = 1/y_1 with y_1 = a_1 + 1/y_2 > 1.
- S computes α. The convergents are computable, and |α − p_k/q_k| < 1/q_k², where q_k ≥ F_{k+1} → ∞.
- α computes S.
  - α = (p_k y + p_{k−1})/(q_k y + q_{k−1}) with y = y_{k+1}.
  - y = a_{k+1} + 1/y_{k+2} with y_{k+2} > 1, so y ∈ (a_{k+1}, a_{k+1}+1).
  - The Möbius map is strictly monotone on y > 0, since p_k q_{k−1} − p_{k−1} q_k = ±1 and q_k y + q_{k−1} > 0.
  - So a_{k+1} = 1 iff α lies on one side of r_k = image of y = 2, and which side is fixed by the parity of k.
  - The comparison is strict because α is irrational, so it terminates from rational approximations.
  - The case k = 0 uses p_{−1}/q_{−1} = 1/0 and gives α = 1/y_1.

PASS.

## 4. Route `every-turing-degree-simple-kazhdan-lef-via-continued-fractions`
- It requires `continued-fraction-real-realizes-every-turing-degree` (PASS above),
  `subshift-elementary-group-word-problem-equals-language`, `sturmian-language-is-turing-equivalent-to-angle` and
  `simple-kazhdan-lef-group-from-minimal-subshift`. The last three exist on main with proof routes, and the owner
  reports them reviewed PASS.
- Steps 1-4 compose correctly.
- The degree of the word problem does not depend on the finite generating set, so distinct degrees give
  nonisomorphic groups.

PASS.

## 4b. Proposal A: LaTeX replacing l.229-262 (`sk-word-problem-proposal-2026-09-13.md` §1)
Checked sentence by sentence.
- **Corollary statement.** WP(G_X) ≡_T L(X) for every infinite minimal X, every degree occurs, and so there are
  continuum many pairwise nonisomorphic G_X. TRUE, and stronger than the current wording at l.232-234.
- **Upper bound.** Tables are formal functions on words; uf = (f∘T^{−1})u, and likewise u^{−1}f = (f∘T)u^{−1}. An
  entry vanishes in R iff each table vanishes on the words of L(X) of its length. TRUE.
- **Lower bound.** e_12(∏_{t<n} u^{−t}e_{v_t}u^t) is computable by iterated commutators. The product is the cylinder
  indicator, since u^{−t}e_a u^t = e_{[x_t=a]}. TRUE.
- **The coding.** c(y)_t = 1 iff y + tα mod 1 ≥ 1−α. The coordinate t switches at y ≡ −tα and y ≡ −(t+1)α, so the
  words of length n are the values on the n+1 arcs cut out by −jα, 0 ≤ j ≤ n. Closure adds no new words. TRUE.
- **Balance.** ⌊y+(t+1)α⌋ − ⌊y+tα⌋ = 1 iff frac(y+tα) ≥ 1−α, so the number of ones is ⌊y+nα⌋, which lies in
  (nα−1, nα+1) for y ∈ [0,1). So any word of length n gives α within 1/n. TRUE.
- **The continued fraction sentence.** TRUE (§3).
- **Line count.** l.229-262 is 34 lines, and the replacement is 28 lines. −6 lines, verified.

**Repairs.**
- (4.i) The proof drops the current text's "There are continuum many degrees". The corollary's "continuum many" needs
  it (2^ℵ0 sets and countable degrees). Put it back: "There are continuum many degrees, and the degree of the word
  problem is an isomorphism invariant." This costs +0 to +1 line.
- (4.ii) Optional. "a word for $e_{12}$ of the cylinder indicator $\prod_{t<n}u^{-t}e_{v_t}u^t$" makes the "trivial
  iff $v\notin L(X)$" step immediate for the reader.
- (4.iii) Calibration only, no text change. The artifact's finding "GAP (minor), l.255-256 … needs both values to
  occur" is overstated. The minimum ⌊nα⌋ needs only ⌊θ+nα⌋ ≥ ⌊nα⌋ and attainment at θ = 0. The replacement's "within
  1 of nα" is correct in any case.

**Integration note for main.** With repair 4.i, Proposal A subsumes sk-referee-2's proposals P5, P6 and P7 for
l.238-261: it defines X_α, gives the computation behind the oracle, and uses a uniform choice of α. sk-referee-2
withdraws P5-P7 in favor of Proposal A.

## 5. `full-group-word-problem-iff-recursive-language` (+ `-citation`)
**Claim.** For a minimal subshift (Ω,T) over a finite alphabet, the derived topological full group G'_T has
decidable word problem iff L(Ω) is recursive (Grigorchuk–Medynets, J. Algebra 500 (2018), Theorem 1.1(3)).

**Independent check.**
- I fetched arXiv:1508.04454 on MSI and extracted it with `gs txtwrite` into
  `/scratch.global/sauer354/sk/sk-referee-2/gm15.txt`. The extraction drops primes and subscripts.
- Abstract (text l.14-15): "the word problem in a topological full group is solvable if and only if the language of
  the underlying subshift is recursive."
- Theorem 1.1, setting: "Let (Ω,T) be a minimal subshift over a finite alphabet. (1) There exists n ≥ 3 such that the
  commutator subgroup of the topological full group G_T is isomorphic to …".
- Item (3) (text l.88-90): "The group G'_T has decidable word problem if and only if L(Ω) is recursive." The prime on
  G'_T is lost in the extraction.
- Crossref, doi:10.1016/j.jalgebra.2016.10.027: "Presentations of topological full groups by generators and
  relations", Journal of Algebra 500, pages 46-68, authors Grigorchuk and Medynets, published April 2018. CONFIRMED.

**Verdict.** PASS. The quotes in the citation route match the source, and the claim restates them with the right
scope (the derived group, minimal subshifts, decidability only). The route honestly says the journal version was not
compared, and the arXiv statement is what is imported.

**For main.** This is prior art at the level of decidability for the amenable simple group of the same subshift. Citing
it next to the note's word-problem corollary is accurate credit, and the degree-level statement for G_X remains new
within sk-novelty's bound. It fits Proposal A (§4b) as one citation clause, e.g. after "so $L(X)$ computes the word
problem": "(for the derived topological full group, decidability is~\cite[Theorem~1.1(3)]{GM18})". The wording
belongs to sk-exposition or sk-novelty.
