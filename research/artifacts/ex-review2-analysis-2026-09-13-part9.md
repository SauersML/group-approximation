# EX review wave 2, part 9: a nontrivial R-fibre W*-bundle, and CCEGSTW Questions 1.5 and 5.29 (2026-09-13)

Lane `ex-verify2-analysis`. Priority review requested by main. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0.

**Landings.** Lane ex2-tw-unsplittable-tails: `4934442568`, `5d7a81c90d`, `761da1070c`, `de1f264555`, `d1913c9e9e`
and `6bfae2597e`.

**Sources read.**
- `research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md` and its part 2.
- BBSTWW, arXiv:1506.03974 (MSI extraction): Question 3.14, Definition 3.1, the strict-separability remark and the
  morphism definition (3.2), all verbatim.
- Ozawa, arXiv:1304.3523, Section 5: the axioms (1)--(3) of a continuous W*-bundle, verbatim.
- CCEGSTW, arXiv:2310.20594v6: Question 1.5 and the "Open" row of their regularity table; Theorem 1.2 and the sentence
  after it ("via Connes' theorem ..."); Definitions 3.8, 4.1 and 5.19; Propositions 3.14, 3.23(iii)--(iv), 5.20 and
  5.27; Question 5.29. All verbatim.
- Toms, arXiv:2606.12188v2, Theorem 5 (checked against the text in part 2 of this review).

## 9.1 Verdicts

| claim or route | verdict |
|---|---|
| `pauli-tower-sections-are-somewhere-scalar` (Theorem A) | PASS |
| `pauli-tower-bundle-has-scalar-point-property` (Theorem B) | PASS |
| route `nontrivial-w-star-bundle-via-pauli-tower` into root `nontrivial-w-star-bundle-with-r-fibres-exists` (BBSTWW Q3.14) | PASS, fidelity confirmed |
| `pauli-tower-bundle-has-no-uniform-order-zero-m2` (Theorem C, C2) | PASS |
| refutation of `r-fibre-w-star-bundles-divide-the-unit-uniformly` | PASS |
| `toms-winter-bauer-tlfnd-via-bundle-halving` cannot fire as stated | PASS |
| `amenable-factorial-ii1-tracially-complete-without-gamma`, routes `q15-negative-via-toms` and `q15-negative-via-bauer-pauli` | PASS |
| `amenable-bauer-factorial-tracially-complete-without-gamma` | PASS |
| imports `nuclear-tracial-completions-are-amenable` and `uniform-gamma-iff-completion-has-gamma` | PASS, quotes verbatim |
| refutation of `ccegstw-q15-amenable-factorial-ii1-has-gamma` | PASS |
| `central-unit-division-without-gamma-exists` (Q5.29) and the refutation of `ccegstw-q529-central-unit-division-gives-gamma` | PASS |

**Not reviewed.**
- Theorem D of part 2 (every prime). It is a sketch, and it appears only as a consequence bullet.
- The "McDuff after one tensor factor" bullet.
- Sections 3--4 of part 2, which are marked heuristic.

## 9.2 Theorem A: PASS

- **Characters.**
  - Ad X fixes X and negates Y and Z; Ad Z fixes Z and negates X and Y. They commute modulo scalars, so V → PU(2) is a
    homomorphism.
  - X, Y, Z carry the characters (0,1), (1,1), (1,0). Pauli strings are an R-basis of Herm(C^{2^r}), and every nonzero
    character of G_r = (Z/2)^{2r} occurs exactly once.
- **Splitting.** E = P_{n,m} ×_{G_r} Herm_0 = ⊕_{χ≠0} λ_χ. Coordinate j = 2k−1 carries g_k, antipodal on the first sphere,
  and j = 2k carries g′_k, antipodal on the second.
  - The sign character on the antipodal cover of RP^d gives the tautological line γ, and the trivial character gives θ.
  - So λ_χ = ⊠_j γ_j^{c_j}, and w_1(λ_χ) = Σ c_j t_j.
- **Top class.** Whitney gives w_{4^r−1}(E) = ∏_{0≠c ∈ F_2^{2r}} (c·t).
- **Moore identity over F_2.**
  - Frobenius is additive, so every nonzero linear form divides det[t_j^{2^i}].
  - The forms are pairwise non-associate primes, and both sides have degree 2^{2r} − 1.
  - The determinant equals Σ_σ ∏_j t_j^{2^{σ(j)}}, with distinct σ giving distinct monomials, so it is nonzero.
  - Check: s = 2 gives t_1 t_2 (t_1 + t_2).
- **Survival.** H*(Z_{n,m}; F_2) = F_2[t_j]/(t_j^{d_j+1}). For σ(j) = j − 2n − 1 the exponents satisfy
  2^{j−2n−1} ≤ 2^{j−1} = d_j, and surviving monomials are basis elements, so nothing cancels.
  - Smallest case (RP¹ × RP²): w_3 = t_1²t_2 + t_1t_2² = t_1t_2² ≠ 0.
- **Conclusion.** A nowhere-zero section of E splits off R, which kills the top class of the rank-(4^r − 1) bundle. The
  "equivalently over Z_m" clause holds because pullback along the projection Z_m → Z_{n,m} is injective on cohomology.
- **Proposition D, re-derived.** For End W, the adjoint bundle's Euler class is pulled back from H^{w²−1}(BU(w); Z). That
  group is 0 in odd degree, and for odd w the class restricts to 0 on BT, where restriction is injective. So the Pauli
  blocks are not End of any vector bundle.

## 9.3 Theorem B: PASS

- **Traces.** Traces of A_m = C(Z_m, B_{0,m}) are ∫ tr(a(z)) dμ, using local matrix units and a partition of unity. The
  maps a ↦ a ⊗ 1 preserve fibre traces.
  - So T(A) = lim Prob(Z_m) = Prob(X̂), and ∂_e T(A) = X̂ is closed.
  - A is a C(X̂)-algebra with fibres M_{2^∞}, so each τ_λ factors through the fibre and π_{τ_λ}(A)″ = R.
- **Bundle.** Ozawa's Section 5 with Theorem 3, through `closed-extreme-trace-sets-give-r-fibre-w-star-bundles` (PASS,
  part 6 §6.2).
- **Variance.**
  - Var_λ(y) = E(y²)(λ) − E(y)(λ)² = ‖π_λ(y) − τ_λ(y)1‖²_{2,λ} is continuous. It vanishes iff π_λ(y) ∈ C1, because
    τ_λ is faithful on π_λ(M) = R.
  - Lipschitz: |τ(y²) − τ(y′²)| ≤ 2C‖y − y′‖_{2,u} and |τ(y)² − τ(y′)²| ≤ 2C‖y − y′‖_{2,u}, so min_λ Var is
    4C-Lipschitz.
- **Limit.** Finite-stage self-adjoint elements have a scalar point (§9.2 with n = 0). Kaplansky density in the uniform
  tracial completion with real parts gives bounded self-adjoint approximants. The minimum is attained by compactness.

## 9.4 Fidelity to BBSTWW Question 3.14: confirmed

- **The question (p. 34, verbatim).** "Question 3.14. Does there exist a nontrivial strictly-separable bundle M over a
  compact metrizable space K all of whose fibres are copies of R?"
- **BBSTWW Definition 3.1 (verbatim).** "A C∗-algebra M is a tracial continuous W∗-bundle over K if: • C(K) is contained
  in the centre of M; • there is a faithful tracial conditional expectation E : M → C(K), defining a norm
  ‖x‖_{2,u} := ‖E(x∗x)‖^{1/2}, called the uniform 2-norm; • the unit ball of M is complete in ‖·‖_{2,u}."
  - Strict separability is ‖·‖_{2,u}-separability ("the natural notion of separability for W∗-bundles"). Ozawa's axioms
    (1)--(3) agree.
- **M meets each axiom.**
  - C(X̂) = lim C(Z_m) is central.
  - E(x)(λ) = τ_λ(x) is a faithful tracial conditional expectation onto C(X̂).
  - The unit ball is complete by construction, and A is separable and dense.
  - The base is ∂_e T(A) = X̂, which is compact metrizable. It is not Prob(X̂).
  - Every fibre is R.
- **Nontrivial.** BBSTWW morphisms (3.2) are *-homomorphisms paired with continuous base maps, intertwining the
  expectations. An isomorphism M ≅ C_σ(K, R) therefore transports Var_λ along the base homeomorphism, so the scalar
  point property would pass to C_σ(K, R). Also, R has a unique trace, so any C(K)-compatible isomorphism intertwines E
  automatically.
- **Status.**
  - BBSTWW record triviality in two cases: finite covering dimension of K ("Ozawa, [65, Corollary 12]"), and M = B^st for
    Z-stable B with Bauer T(B). The witness meets neither: X̂ contains a Hilbert cube, and A is not Z-stable (C3 of part 1).
  - Mommaerts's Remark 4.7 (arXiv:2606.12134), recording existence as unknown, was not re-read here.
- **Numbering discrepancy, no statement at stake.** BBSTWW cite Ozawa's finite-dimensional-base theorem as Corollary 12,
  while the graph node calls it Corollary 16. Not re-checked.

## 9.5 Nontriviality calibration: PASS

In C_σ(X̂, R) the constant section e, a projection of trace 1/2 in R, has Var_λ(e) = 1/2 − 1/4 = 1/4 at every λ, so it is
nowhere scalar. M has no nowhere-scalar self-adjoint element. So the invariant separates M from the trivial bundle, and
the separation is invariant under W*-bundle isomorphisms (§9.4).

**Consistency with the known triviality theorems.** None of them applies:
- finite-dimensional or σ-finite-dimensional bases: X̂ contains a Hilbert cube;
- CCEGSTW Proposition 5.28 (∂_e X totally disconnected): X̂ is connected;
- the Evington--Schafhauser announcement (finite-dimensional ∂_e X);
- local triviality: every open set of X̂ contains full tail factors.

## 9.6 Theorem C, C2, the refutation and the dead route: PASS

- **Theorem C.** Take a scalar point μ1 of a − b with ab = 0.
  - μ > 0 makes π_λ(a) invertible, so π_λ(b) = 0; μ < 0 is symmetric.
  - μ = 0 gives π_λ(a)² = π_λ(a)π_λ(b) = 0.
- **C1.** In the fibre R, φ(e_{ii}) = π(e_{i1})φ(e_{11})π(e_{1i}), with c = φ(1) commuting with π (Winter--Zacharias,
  standard). So the pieces vanish together, and min_λ τ_λ(φ(1)) = 0.
- **C2 (the 1/4 bound).** τ_λ(y) = τ_λ(c)/2 and τ_λ(y²) = τ_λ(c²)/2. From c − c² ≤ 1 − c, τ_λ(c²) ≥ 1 − 2ε_λ, so
  Var_λ(y) ≥ 1/4 − ε_λ > 0.
- **Reduced power.** A unital M_2 ⊆ M^ω lifts to order zero maps with ‖E(1 − φ(1))‖ → 0, which is excluded.
- **Refutation.** `r-fibre-w-star-bundles-divide-the-unit-uniformly` asserts such maps in every R-fibre bundle for every N
  and ε, and M fails it at N = 2. The node already carries `refuted_by`.
- **Dead route.** `toms-winter-bauer-tlfnd-via-bundle-halving` requires that refuted claim, so it cannot fire. The target
  `toms-winter-holds-on-bauer-tlfnd-locus` stays open. A version restricted to strict closures of simple algebras with
  strict comparison is untouched, as the node says.

## 9.7 CCEGSTW Question 1.5: PASS on both routes

- **The question (verbatim).** "Question 1.5. Does every amenable type II1 factorial tracially complete C∗-algebra satisfy
  property Γ?" Their table lists "Amenable factorial II1 tracially complete C∗-algebra" as "Open".
- **Definitions (verbatim).**
  - Definition 3.8: "(M,X) is of type II1 if π_τ(M)″ is a type II1 von Neumann algebra for every τ ∈ X."
  - Definition 3.13: "factorial if X is a closed face of T(M)."
  - Proposition 3.14: factorial iff π_τ(M)″ is a factor for every extreme τ ∈ X.
  - Proposition 3.23(iii)--(iv): the completion (A^X, X̃) is tracially complete, and it is factorial iff X is a face in
    T(A).
  - Definition 4.1 (tracially nuclear, amenable); Theorem 1.2 with "via Connes' theorem, the uniform tracial completion
    of a nuclear C∗-algebra is amenable".
  - Definition 5.19 (property Γ); Proposition 5.20 (uniform Γ ⟺ Γ of the completion over T(A), T(A) compact).
- **Toms route.** B is Toms's simple unital separable nuclear AH algebra without uniform Γ (Theorem 5).
  - Its completion over X = T(B) is tracially complete and factorial (3.23(iii)--(iv); T(B) is a face of itself), and
    amenable (Theorem 1.2 sentence).
  - Type II_1: a finite von Neumann algebra π_τ(B)″ with a type I_n summand gives, through a character of the centre, a
    unital representation B → M_n, which simple infinite-dimensional B does not have.
  - No Γ by Proposition 5.20.
  - **Credit.** This is an immediate corollary of Toms's Theorem 5 and CCEGSTW Proposition 5.20. CCEGSTW v6 (7 Aug 2026)
    lists the question as open, and its text cites only older Toms papers. It should be described as "Toms's example
    answers Question 1.5 negatively through Proposition 5.20", credited to Toms. Experts may already know it; no novelty
    check was run here.
- **Pauli route.** (M, X) is the completion of the Pauli algebra over X = Prob(X̂).
  - It is tracially complete and factorial (3.23; T(A) is a face), amenable, and type II_1: A has no finite-dimensional
    representation, since every irreducible representation factors through a fibre M_{2^∞}.
  - **No projection of constant trace 1/2 in M^ω.**
    - Represent p by positive contractions x_n = f(Re x′_n). Traces at limit traces force
      lim_ω sup_τ |τ(x_n) − 1/2| = 0, and sup_τ τ(x_n − x_n²) ≤ ‖x_n − x_n²‖_{2,X} → 0.
    - At a scalar point μ = τ_λ(x_n), τ_λ(x_n − x_n²) = 1/4 − (μ − 1/2)² ≥ 1/4 − η².
  - So Definition 5.19 fails already for S = {1} and k = 2.
  - What it adds over Toms: a **Bauer** designated trace set, and no projection of trace 1/2 at all, central or not.
    This is consistent with Proposition 5.27, whose central-division hypothesis fails here.

## 9.8 CCEGSTW Question 5.29: PASS

- **The question (verbatim).** "Question 5.29. Does Proposition 5.27 hold for all factorial tracially complete
  C∗-algebras (i.e. without assuming that X is a Bauer simplex)?" Proposition 5.27 is verbatim on the node.
- **Witness.** Toms's B over its Poulsen T(B).
  - Block projections e^{(j)}_b of equal rank, with L_j → ∞, commute exactly with μ(B_{m_j}) (part 6 §6.1).
  - Grouping them gives orthogonal q^{(j)}_i, norm-central along j, with sup_τ |τ(q_i) − 1/k| ≤ k/L_j. So p_i ∈ M^ω ∩ S′
    have trace 1/k on every limit trace, hence on X^ω.
  - Γ fails by Proposition 5.20 and Theorem 5.
  - Credit: Toms and CETW Proposition 5.10, as the node records. The CETW Question 3.5 remark (n = 2) is correct.

## 9.9 Owner notes (sent), no statement changes

- Theorem D (every prime) is listed as a consequence bullet on the established `pauli-tower-sections-are-somewhere-scalar`.
  It is sketch-level and unreviewed; keep it out of any "established" reading.
- The "McDuff after one tensor factor" bullet was not re-derived.
- The Q1.5 framing should credit Toms's Theorem 5 for the first route, as the nodes already do.
