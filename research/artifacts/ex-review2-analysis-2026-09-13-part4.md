# EX review wave 2, part 4: the RR0 dichotomy lanes (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. The scope is the 14 census
claims of ex-rr0-dichotomy and ex-rr0-tarski-ideals.

**Sources re-checked.** Fetched to `/scratch.global/sauer354/ex/ex-verify2-analysis/` and extracted with ghostscript.
- Rainone, arXiv:1502.06153: Proposition 4.17 is verbatim. Its hypotheses are "A has cancellation and K_0(A)^+ has the
  Riesz refinement property", and it proves (1) ⟺ (2) ⟺ (3), with (3) "θ = [g] is infinite".
- Ortega--Perera--Rørdam, arXiv:0904.0541: Corollary 5.16, Proposition 5.17 and Theorem 4.3 are verbatim.
- Ara--Goodearl, arXiv:1405.7582: Theorem 2.3 is verbatim.
- Not re-grepped: Rainone Theorems 4.13, 4.16, 4.21 and 4.22, and OPR Corollary 4.4. Their quotes are consistent with
  the surrounding text.
- Not re-read: the Rørdam 2005 manuscript, whose quotes match the published abstract.

**Root check.** `stw99-problem-xxix-rr0-dichotomy` stays open. Its four routes need open prerequisites: weak
cancellation, corona factorization, Problem LX or Problem XXX.

## 4.1 Literature imports: six PASS

- **`ara-goodearl-tame-refinement-monoids-separative`: PASS.** Theorem 2.3 and Definition 2.1 are as quoted.
- **`opr-cfp-rr0-dichotomy`: PASS.** Corollary 5.16 is verbatim, and Theorems 5.8(ii) and 5.14 are consistent.
- **`opr-mixed-simple-refinement-monoid`: PASS.** Proposition 5.17 is verbatim, with the proof via M_0 = {0, u, ∞}.
- **`opr-properly-infinite-multiple-splits`: PASS.** Theorem 4.3 is verbatim. The last paragraph is the lane's own
  elementary argument and was re-derived: e ~ p ⊕ p′ gives orthogonal subprojections of e with the two classes.
- **`rainone-type-semigroup-crossed-product-dichotomy`: PASS as an import.** The Theorems 4.21 and 4.22 quotes were not
  re-grepped. Proposition 4.17, which is used downstream (§4.10), is verbatim.
- **`rordam-mixed-examples-not-real-rank-zero`: PASS as an import, not re-read here.** The abstract quoted in the route
  matches the published statement. The mechanism is described, not claimed as new.

## 4.2 `coinvariant-tarski-lemma-minimal-nowhere-scattered`: PASS

Re-derived.
- **Step 1.** L = {y ≤ Σ_j α_{t_j}(x)} is hereditary, additive and invariant. H = L − L is convex with H ∩ G^+ = L, so
  minimality gives H = G and [y] ≤ n[x].
- **Step 2.** Nx + e ~ Nx is stable under translating e and under adding defects. By Step 1, x ≤ E = Σα_{s_k}(e), so
  some pieces c_i satisfy Σc_i = Nx and Σα_{t_i}(c_i) = Nx + E.
- **Step 3.** (ND) with M = N + 2 gives d_i and f_i = c_i − N d_i with M f_i ≤ c_i.
- **Step 4.**
  - N(x − Σd_i) = Σf_i ≥ 0, so r ≥ 0 by (P), and x ~ x′ = Σα_{t_i}(d_i) + r.
  - N(x′ − x) = h + Σf_i with h = E − Σα_{t_i}(f_i).
  - Mh ≥ ME − Σα_{t_i}(c_i) = ME − Nx − E ≥ (M − N − 1)E = E, using Nx ≤ NE. So h ≥ 0, and h ≠ 0 by conicality.
  - Hence e′ = x′ − x ∈ G^+ ∖ {0}, and [x] = [x] + [e′].
  - The bound is independent of the number of pieces, which is the point of the lemma.
- **Step 5.** [x] = [x] + k[e′] ≥ 2[x] for k with k[e′] ≥ [x].

## 4.3 `af-k0-order-divisible-iff-no-elementary-subquotient`: PASS

- **2 ⟹ 1.**
  - If no finite stage has only large blocks, every small block is fed only by small blocks, and at least one feeds
    it, since 1_B ∈ B_m.
  - Kőnig's lemma gives an infinite chain of small blocks. Its sizes stabilize with multiplicity one, so the maps
    π_m are compatible and define a unital representation B → M_k.
  - In blocks of size k ≥ NM, the quotient-rank piece q gives N[q] ≤ [1] and a remainder r < N per block with Mr < k.
- **1 ⟹ 2.** Ranks under an irreducible σ with σ(1_B) = 1, taking N = 2k and M = 2.
- **3 ⟹ 2.** An irreducible representation extends from the corner and contains the compacts. Ideals of D ⊗ K are
  I ⊗ K, so J/I is elementary.
- **2 ⟹ 3.** Lift a rank-one projection of J/I to p ∈ J. Then pDp → Ce is a one-dimensional representation, and
  pAp = pDp.

## 4.4 `dimension-group-divisible-iff-no-integer-subquotient`: PASS

- Effros--Handelman--Shen realization, and Elliott's ideal correspondence I ↦ K_0(I) with K_0(J/I) = K_0(J)/K_0(I).
- Lifting of projections gives the positive cone of the quotient.
- A simple AF algebra with K_0 = (Z, N) has a minimal projection, hence is elementary.

## 4.5 `nowhere-scattered-af-crossed-products-dichotomy`: PASS

- **Hypotheses.** Exact, real rank zero, (SP), total projections, cancellation and a dimension-group K_0 all hold. (ND)
  comes from §4.3. Minimality ⟺ no invariant order ideals is Rainone Theorem 3.7, since every ideal of D has a
  projection.
- **Case A.** A nontrivial state is finite by minimality and faithful after pulling back to K_0. Theorem 4.13 gives an
  invariant faithful trace and stable finiteness.
- **Case B.** Tarski plus §4.2 make Σ purely infinite, and Theorem 4.21 (1) ⟹ (3) gives pure infiniteness.
- **Exclusivity.** The null set of an invariant trace is a proper invariant ideal, hence 0.

## 4.6 `nowhere-scattered-af-integer-crossed-products-dichotomy`: PASS, one note

- **Minimality and simplicity.** Elliott's correspondence is equivariant, so α_* is minimal on K_0. Kishimoto and
  Olesen--Pedersen give simplicity.
- **(P1).** Rørdam 2005 Lemmas 5.1 and 5.4 compress her_A(a) onto a hereditary subalgebra of D, which has a projection.
  These lemmas were not re-read.
- **(P3).** A faithful invariant positive homomorphism K_0 → R is the K_0-map of a unique densely finite lower
  semicontinuous trace on the AF algebra, and it is invariant by uniqueness. Then τ∘E is faithful on simple A.
- **(P4).** Every nonzero projection of D ⊗ K is infinite in A ⊗ K. By (P1) every hereditary subalgebra has an infinite
  projection, and an infinite projection of A ⊗ K lying in A is infinite in A.
- **Note.** The route says "(P2) is unchanged" from `simple-af-integer-crossed-products-dichotomy-proof`, which has a
  PASS. Re-derived here: equidecomposable classes give Murray--von Neumann equivalent projections in A, and
  [x] = [x] + [e′] with e′ ≠ 0 gives an infinite projection. Only the argument is borrowed, not a claim, so the
  `requires` list is complete.

## 4.7 `rr0-sr1-coefficient-crossed-products-dichotomy`: PASS

- **K_0 is a dimension group.** Real rank zero and stable rank one give refinement, cancellation, (SP) and total
  projections. K_0(A)^+ is conical by stable finiteness. K_0 is countable, directed, interpolated and unperforated,
  hence a dimension group by EHS.
- **(ND)** follows from §4.4.
- **Rest.** §4.5 verbatim, since it used only Rainone's listed hypotheses.
- **Example.** C(X) ⊗ A_θ = lim ⊕ A_θ for totally disconnected X, with K_0 = C(X, Z + θZ) ordered pointwise. Its
  subquotients are C(V, Z + θZ), never (Z, N).

## 4.8 `minimal-normal-cyclic-subgroup-cantor-dichotomy`: PASS

- **Step 1.** For f = Σc_i and g = ΣT^{k_i}c_i, telescoping gives f − g = h − Th.
  - h is locally constant and the bases B_n shrink to x_0, so h is eventually constant on T^{-1}B_n.
  - Along a tower the sum of h − Th is h(T^{J−1}c) − h(T^{-1}c) = 0. Both points lie in T^{-1}B_n, since T^J C_τ ⊆ B_n.
  - So S(X, H) is the positive cone of lim Z^{towers} = K^0(X, T).
  - It is simple by minimality, and noncyclic because μ(B_n) → 0 while [1_{B_n}] ≠ 0.
- **Step 2.** Normality makes Γ act on K^0(X, H). Cancellation in S(X, H) lifts equidecomposability.
- **Steps 3--4.** The lemma applies to the simple noncyclic dimension group. States correspond to invariant
  measures, and Rainone Theorems 4.13 and 4.21 apply.

## 4.9 `smoothing-normal-subgroup-cantor-dichotomy`: PASS

- **Step A, orbit sums.** Induction on |F|. At a point with full stabilizer, f and g are constant and equal near it on
  an invariant clopen set.
  - Otherwise a K-invariant clopen U with tU ∩ U = ∅ for t ∉ K reduces to K, and F y ∩ U = K y.
  - Invariant clopen subsets keep their kind, since W = F(W ∩ U). So the regions can be made disjoint.
  - The positive orbit-sum cone is attained by N-valued functions. So S(Y, F) is cancellative with pointwise order, and
    refinement lifts from C(Y, N).
- **Step B.** Locally finite H: equidecompositions use finitely many elements, so S(X, H) = lim S(X, H_n).
  - The limit is simple by minimality.
  - It is noncyclic: an invariant measure is atomless because orbits of a minimal action on the infinite space X are
    infinite, and it has full support.

## 4.10 `af-crossed-product-counterexample-normal-form`: PASS

- **Parts 1--3.** Contrapositives of §4.5.
  - For amenable Γ, the affine action on the nonempty compact convex T(D) has a fixed point.
  - A nontrivial state on Σ gives an invariant trace. A purely infinite Σ makes A purely infinite.
- **Part 4.**
  - Theorem 4.16 gives a nonzero projection p ∈ D that is not properly infinite in A.
  - In a simple algebra an infinite projection is properly infinite: the orthogonal copies v^i e v^{*i} of the full
    defect e, with p ≾ e ⊗ 1_n, give p ⊕ p ≾ p. So p is finite.
  - If θ = [p] were infinite, Proposition 4.17 (3) ⟹ (1), checked verbatim, would make p properly infinite in A. D is
    AF, so cancellation and refinement hold. So θ is finite.
  - Tarski with part 3 gives (k+1)θ ≤ kθ.
- **Part 5.** Choose m with u = 2^mθ finite and 2u infinite, hence properly infinite, and write 2u = 4u + w.
  - With x = u and y = u + (2u + w): x + y = 2u = 2x, and 2y = 6u + 2w = 2u + (4u + w) + w = 4u + w = 2u.
  - x ≠ y, since otherwise u would be infinite.
- **Parts 6--7.** These follow from the named nodes and from simplicity with real rank zero of M_n(A).
- The node correctly marks part 4 as not certifying finiteness in A by itself.

## Notes

- **Novelty.** The lanes mark it unchecked beyond Rainone 2017 and Rørdam 2005. Nothing further was checked here.
- **Owner messages.** No finding needs a correction or an owner message.
