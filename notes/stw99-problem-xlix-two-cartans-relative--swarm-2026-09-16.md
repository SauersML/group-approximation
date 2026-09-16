# stw99-problem-xlix-two-cartans-relative-gamma --- swarm pass, 2026-09-16

Agent: `swarm-stw99-problem-xlix-two-cartans`. Lock held on the root for this pass.

**Target (OPEN, root).** STW Problem XLIX: does some unital simple separable nuclear `A` contain Cartan
subalgebras both with and without relative uniform property Γ?
- The problem is not solved.

**Outcome: obstruction.** Every witness has infinitely many extremal traces.
- Proved in full: every Cartan subalgebra of a unital simple separable nuclear infinite-dimensional
  algebra with `1 <= |∂_e T(A)| < ∞` has relative uniform Γ. By KLTV Corollary 5.3, it also has CPoU.
- Also recorded: dead ends and exactly where each dies.

**New nodes (uncommitted, for the referee).**
- claim `research/cartan-pairs-finite-extremal-traces-have-relative-gamma.md`;
- route `research/cartan-pairs-finite-extremal-traces-have-relative-gamma-proof.md`, with `requires: []`;
- artifact `research/artifacts/cartan-finite-extremal-relative-gamma-2026-09-16.md`, which holds the full
  proof.

## 1. Setup

**Definition.** Relative uniform Γ, from KLTV arXiv:2406.09808v4, Definition 3.5 (text read 2026-09-16).
- Standing hypotheses: `A` separable, `T(A)` nonempty and compact.
- `(D ⊆ A)` has uniform Γ if `κ(D^U) ⊆ A^U` is unital and, for each `k`, there are projections
  `q_1, ..., q_k ∈ κ(D^U) ∩ A'`, summing to `1`, with `tau(q_i a) = tau(a)/k` for all limit traces
  `tau` and all `a ∈ D`.
- `A^U` is the uniform tracial ultrapower (KLTV (2.2)).

**What the repository had.**
- The root claim and its presentation artifact `research/artifacts/stw99-presentations-cartan-cluster-2026-08-30.md`.
- The known failing example: Giol–Kerr positive mean dimension systems. There `(C(X) ⊆ C(X) ⋊ Z)` fails
  relative Γ by KLTV Corollary D.
  - Their crossed products nevertheless have absolute uniform Γ
    (`giol-kerr-crossed-products-have-uniform-gamma`, ESTABLISHED).
  - So relative Γ of one Cartan is strictly stronger than absolute Γ of `A`.
- For free amenable actions (KLTV Theorem 5.4, text read 2026-09-16), the following are equivalent:
  - the small boundary property (SBP),
  - relative Γ,
  - CPoU.
- Nothing in the graph controlled Cartan subalgebras that do not come from group actions.

**Duplicate search.**
- `bin/cairn search` for "Cartan relative uniform Gamma" and similar queries turned up only the root, the
  Giol–Kerr and Villadsen nodes, and the Barlak–Li UCT citations.
- `bin/cairn search --similar` aborted on another agent's broken `distinct_from` in
  `research/column-model-kazhdan-cut-downs-certify-only-lef.md`, so the similarity check was done by Grep
  over `research/`.
- No node states anything about Cartan pairs with finitely many extremal traces.

## 2. What was proved

**Theorem** (`cartan-pairs-finite-extremal-traces-have-relative-gamma`). Let `A` be unital, simple,
separable, nuclear and infinite-dimensional, with `1 <= |∂_e T(A)| < ∞`, and let `D ⊆ A` be a Cartan
subalgebra.
- Then `(D ⊆ A)` has KLTV uniform Γ.
- The dividing projections satisfy (3.3) for **all** `a ∈ A`.
- By KLTV Corollary 5.3(ii), `(D ⊆ A)` has CPoU.

**Corollary for XLIX.**
- `T(A) = ∅`: Definition 3.5 does not apply.
- `A = M_d`: no Cartan has relative Γ, because `κ(D^U) ∩ A' = C1`.
- Finitely many extreme traces: the Theorem gives every Cartan relative Γ.
- So a witness must have infinitely many extremal traces.

**Proof architecture** (full details in the artifact).
1. `T(A) = conv{tau_j}`, so the uniform 2-norm is `max_j ‖·‖_{2,tau_j}`.
2. **Commutator formula.** Kumjian's relation `n^* d n = (d∘α_n) n^*n` gives
   `[n,f]^*[n,f] = (f − f∘α_n)^2 n^*n`. So everything about `D`-central sequences is controlled by the
   measures `μ_tau = tau|_D` and the Weyl pseudogroup. No trace needs to factor through `E`.
3. **The trace measures.** The trace property makes each `μ_tau` invariant under every `α_n`.
   - Simplicity makes each `μ_tau` nonatomic.
   - Proof of nonatomicity: an atom gives a finite closed invariant orbit `F`. If `F ≠ X`, a regular
     representation `π_x` kills a nonzero `d ∈ D`. If `F = X`, effectiveness makes `G` finite and
     principal.
4. **Hyperfiniteness.** Nuclear implies `G` amenable (Takeishi Theorem 5.4, as quoted in Barlak–Li).
   - Continuous approximately invariant means push forward along `s` to a Borel Reiter sequence on the
     orbit relation `R`.
   - Connes–Feldman–Weiss then gives `μ`-hyperfiniteness.
5. **Balancing.** Take a finite subrelation `R_l` capturing the test normalizers off a small set.
   - On a Borel transversal of `R_l`, apply Lyapunov's theorem to the nonatomic vector measure
     `(μ_j([·]_{R_l}))_j`.
   - This gives exactly balanced, almost invariant Borel partitions.
6. **Continuity.** Urysohn functions with `Σ f_i = 1`; the formula of step 2 bounds the commutators.
7. **Assembly.** Take a diagonal sequence.
   - For each extremal `tau_j`, `a ↦ lim tau_j(f_i^(r) a)` is tracial and dominated by `tau_j`, so it
     equals `tau_j/k`.
   - This gives (3.3) for every `a ∈ A`.

**By-products, proved or sketched in the artifact.**
- **Trace-restriction principle** (proved; a direct consequence of step 2). Whether `(D ⊆ A)` has
  relative Γ depends only on:
  - the spectrum `X`;
  - the partial homeomorphisms `α_n` with weights `n^*n`;
  - the set `T(A)|_D` of trace measures.
  Relative Γ is therefore a property of the "Weyl pseudogroup plus trace-measure set". This is the right
  frame for XLIX: the two Cartans must give different pairs (pseudogroup, measure set), each measure set
  a continuous affine image of `T(A)`.
- **Local relative Γ** (sketch, Remark 1 of the artifact). For any finite `S ⊆ T(A)`, relative Γ holds in
  `(A, S)^U`. The proof balances finitely many test functions of `D` in Lyapunov's theorem. So failure of
  relative Γ is purely a failure of uniformity over infinitely many traces, parallel to Toms's absolute
  failure.
- **Absolute Γ.** Since (3.3) holds for all `a ∈ A`, KLTV Remark 3.7 gives absolute uniform Γ of `A` in the
  finite-extremal case, for every algebra with a Cartan.

## 3. Consistency checks

- **Giol–Kerr.**
  - Free minimal `Z`-systems of positive mean dimension fail relative Γ (KLTV Corollary D).
  - So they must have infinitely many ergodic measures.
  - This agrees with Kerr–Kopsacheilis–Petrakos, arXiv:2404.04634v2, as abstracted in
    `research/artifacts/lit-major-findings-2026-09-12.md`: a closed finite-dimensional extreme boundary
    gives SBP for minimal actions.
- **Villadsen algebras of the first type.**
  - Canonical Cartans with positive coordinate weight fail relative Γ, per the repository's record of
    Elliott–Niu (not re-read).
  - They must then have infinitely many extreme traces.
  - Sketch: positive weight on identity coordinates makes `T(A)` infinite-dimensional (every product
    measure on the base spaces survives).
- **`M_d`.** The theorem needs infinite-dimensionality, and the corollary handles `M_d` separately.
- **SBP.** For a finite set of nonatomic measures, the `M`-small boundary property is automatic: balls
  `B(x,r)` have null boundary for all but countably many `r`. So KLTV Proposition 4.5 (CPoU ⟹ SBP)
  gives nothing new here, as expected.

## 4. Approaches tried and exactly where each dies

**A. Build the witness from a Giol–Kerr algebra with a second, dynamical Cartan.**
- The approach: let `A = C(X) ⋊ Z` be Giol–Kerr, so its canonical Cartan fails relative Γ, and look for
  `A ≅ C(Y) ⋊_β H`, where `β` is free minimal with SBP.
- By KLTV Theorem 5.4, relative Γ for `C(Y)` means SBP for `β`.
- **Dies when `H` has polynomial growth.**
  - Naryshkin (dynamical comparison for polynomial growth groups; not fetched) plus Kerr–Szabó (SBP +
    comparison gives almost finiteness; not fetched) make `β` almost finite.
  - Kerr (almost finite free minimal gives `Z`-stable crossed products; not fetched) then makes `A`
    `Z`-stable.
  - But Giol–Kerr algebras are not `Z`-stable.
- **What survives:** the second Cartan would have to be non-dynamical, twisted, or from a group without
  known comparison.
- Nothing in this pass constructs one.

**B. A `Z`-stable ambient algebra containing a positive mean dimension Cartan.**
- The approach: start from a `Z`-stable `A`, which has a Cartan with relative Γ in favourable cases, and
  find a failing Cartan of the form `C(X) ⊆ C(X) ⋊ Z` with `mdim > 0`.
- **Dies:** this needs a free minimal `Z`-system with positive mean dimension and a `Z`-stable crossed
  product.
  - That refutes the Phillips–Toms conjecture (`stw99-problem-xxxvi-phillips-toms`: `rc = mdim/2` would
    force `rc > 0`).
  - It also refutes the optimistic characterisation recorded at
    `stw99-problem-xxxiv-dynamical-characterisation`.
- So this route is at least as hard as disproving open conjectures. It is not ruled out.

**C. Tensor products.**
- The approach: `A = A_1 ⊗ A_2` with Cartans `D_1 ⊗ D_2` and `D'_1 ⊗ D'_2`.
- **Dies:** if `(D_2 ⊆ A_2)` has relative Γ, so does `(D_1 ⊗ D_2 ⊆ A_1 ⊗ A_2)`.
  - Use the projections `1 ⊗ q_i`.
  - For positive `a ∈ A_1`, the functional `b ↦ tau(a ⊗ b)` is a positive tracial functional on `A_2`.
  - The (3.3) convergence is uniform over `T(A_2)`, since otherwise a violating limit trace exists.
  - Only sketched here, with no node.
- So a product-Cartan witness needs both factors failing on one side. The second Cartan must genuinely
  mix the tensor factors, and tensoring cannot manufacture it.

**D. A C\*-analogue of Connes–Jones infinite tensor products with two Cartans.**
- **Dies:** tail factors supply `D`-central sequences.
- Uniform division over all traces then reduces to an SBP-type uniform division inside the factors, which
  is the original problem again.
- No gain.

**E. Extending the theorem to compact, finite-dimensional `∂_e T(A)` (KKP analogue for arbitrary
Cartans).**
- **The approach:**
  - Local solutions from Remark 1 are stable under weak\*-perturbation of the trace. For fixed `f_i ∈ D`,
    the maps `tau ↦ tau((f − f^2)^2)`, `tau ↦ tau([n,f]^*[n,f])` and `tau ↦ tau(f d)` are continuous.
  - So each trace has a neighbourhood on which a fixed local solution works.
  - Compactness gives finitely many neighbourhoods. Glue them with KLTV weak CPoU, which holds for Cartan
    pairs by KLTV Theorem 5.2.
- **The error elements are in `D_+`**, as Definition 4.2 requires.
  - This uses the commutator formula.
  - It needs a small check for the balancing errors.
- **Dies at orthogonality.**
  - Weak CPoU gives positive contractions `e_t ∈ κ(D^U) ∩ S'` summing to `1`, not orthogonal projections.
  - The glued `F_i = Σ_t e_t f_i^t` is balanced but is not a near-projection: `F − F^2` contains the cross
    terms `e_t e_s f^t f^s`.
  - Upgrading `e_t` to projections is what relative Γ itself provides, so the argument is circular. KLTV
    Proposition 4.4 (weak CPoU + uniform Γ ⟹ CPoU) and the surrounding text say "the gap between CPoU
    and weak CPoU is precisely uniform property Γ".
- **Independent evidence the gluing cannot be formal.**
  - In the absolute setting, `(A ⊆ A)` has weak CPoU for every nuclear `A` with compact nonempty `T(A)`
    (KLTV attribute this to [5, Lemma 3.6] = CETW; text read 2026-09-16).
  - Local Γ at finitely many traces holds for every simple nuclear non-elementary `A`. This is standard
    via hyperfiniteness of the GNS closures, but was not re-verified here.
  - Yet Toms's AH algebra lacks uniform Γ (`toms-ah-counterexample-to-uniform-gamma`).
- **What a proof needs:** the finite covering dimension of `∂_e T(A)`, used as in Kirchberg–Rørdam /
  Sato / TWW, or as in KKP's dynamical argument.
- **Candidate next hole** (not created as a node): "Cartan pairs in simple nuclear algebras whose
  `∂_e T(A)` is compact and finite-dimensional have relative uniform Γ."
  - This would be a groupoid version of KKP plus KLTV Theorem 5.4 (i ⟹ ii).
  - The missing ingredient is a Kerr–Szabó style "SBP ⟹ relative Γ" for amenable effective étale
    groupoids.

**F. The E-pushdown lemma (sketch only, not relied upon).**
- **The idea:** push relative-Γ data through `E` to reduce to traces of the form `μ∘E`.
- **Two caveats kill it as a proof:**
  1. `E(p)` of a central-sequence projection can be a scalar sequence, so the pushdown loses the
     partition.
  2. That every `R`-invariant measure `μ` gives a trace `μ∘E` needs a twisted-groupoid argument that was
     not checked.
- The theorem above avoids `E` entirely, via the commutator formula.

## 5. Open directions

1. **Compact finite-dimensional boundary.** Approach E; needs relative orthogonality.
2. **Groupoid SBP ⟹ relative Γ.** An effective étale amenable groupoid with the `T(A)|_D`-small boundary
   property should give relative Γ, by analogy with Kerr–Szabó Theorem 9.4 as cited by KLTV. Combined with
   KLTV Proposition 4.5 and Corollary 5.3, relative Γ would then be equivalent to SBP for all Cartan
   pairs.
   - If so, XLIX becomes: can one algebra have two Weyl pseudogroups, with trace-measure sets, one with
     SBP and one without?
3. **Search for a witness among infinite-trace-simplex algebras with a non-dynamical second Cartan.**
   - Candidates: Giol–Kerr algebras (by A, the second Cartan cannot be a polynomial-growth SBP action), and
     Villadsen-type algebras with alternative diagonals.

## 6. Literature consulted

- **Schafhauser–Tikuisis–White**, arXiv:2506.10902v2, text read 2026-09-16. It poses XLIX as open.
- **Kopsacheilis–Liao–Tikuisis–Vaccaro**, arXiv:2406.09808v4, HTML text read 2026-09-16. Items used:
  - Definitions 3.2, 3.5, 4.1, 4.2;
  - (2.1)–(2.2);
  - Remark 3.7;
  - Proposition 4.5;
  - Theorem 5.2;
  - Corollary 5.3;
  - Theorem 5.4;
  - Corollary D;
  - the attribution of absolute weak CPoU to CETW Lemma 3.6.
- **Barlak–Li**, arXiv:1511.02697v3, text read 2026-09-16. It quotes Takeishi [25, Theorem 5.4]:
  nuclear `C*_r(G, Σ)` implies `G` amenable. Takeishi, Publ. RIMS 50 (2014) 251–268, was not fetched.
- **Kerr–Kopsacheilis–Petrakos**, arXiv:2404.04634v2: only the abstract, via
  `research/artifacts/lit-major-findings-2026-09-12.md`.
- **Not fetched, cited by standard content only (numbering unverified):**
  - Kumjian, Canad. J. Math. 1986;
  - Renault, Irish Math. Soc. Bull. 61 (2008);
  - Anantharaman-Delaroche–Renault, *Amenable groupoids* (2000);
  - Connes–Feldman–Weiss (1981);
  - Kechris–Miller, LNM 1852;
  - Kechris, GTM 156;
  - Lyapunov (1940);
  - Giol–Kerr (Crelle 2010);
  - Naryshkin;
  - Kerr;
  - Kerr–Szabó;
  - Elliott–Niu;
  - Connes–Jones.
- **Search limits:** WebSearch was unavailable (budget exhausted), so 2025–26 literature beyond the texts
  above and the repository audits was not scanned. Priority of the theorem is unverified.

## Referee (2026-09-16)

**Checked.**
- **Step-by-step re-derivation of the artifact's proof.** Every step was re-derived by hand.
  - Lemma 1: the invariance computation, including the division by the positive density `ψ∘α_n^{-1}`.
  - Lemma 2: the commutator expansion `[n,f]^*[n,f] = (f − f∘α_n)^2 n^*n`, recomputed term by term.
  - Lemma 3: nonatomicity.
    - `π_x` kills every `d` vanishing on the finite orbit, and it is unital, so `ker π_x` is a proper
      nonzero ideal.
    - If the orbit is all of `X`, then `X` is finite and discrete, isotropy is open, effectiveness forces
      principality, and `A` is finite-dimensional.
  - Step 2: the Borel Reiter sequence.
    - It is the pushforward `s_*(m^x)`.
    - Its invariance comes from `s_*(γ m^y) = s_*(m^y)`.
    - Borel measurability follows from Borel pieces of bisections.
  - Step 2: the null saturation argument.
  - Step 3: exact simultaneous balance for all `m` measures. Iterating Lyapunov works: at each stage
    `(1/k,...,1/k)` lies on the segment from `0` to the remaining vector mass `(t,...,t)`. Nonatomicity of
    `ν_j` on the standard Borel transversal follows from Lemma 3.
  - Step 4: the Urysohn estimates, including `f − f^2 ≤ |f − 1_B|` and the transfer of the third
    commutator term through Lemma 1.
  - Step 5: the diagonal assembly, and the extremality argument giving (3.3) for all `a ∈ A`.
- **Consistency.**
  - The absolute consequence, uniform Γ with finitely many extreme traces, is the expected behaviour: the
    tracial ultrapower is a finite sum of McDuff central sequence algebras.
  - In the dynamical case, finitely many nonatomic invariant measures give SBP trivially, hence mean
    dimension zero, which is consistent with KLTV Corollary D and Giol–Kerr.
- **Citations fetched.**
  - KLTV arXiv:2406.09808v4.
    - Definition 3.5: (3.3) is required for `a ∈ D` and limit traces `T_U(A)`.
    - (2.1)–(2.3), Remark 3.7, Propositions 4.4 and 4.5, Theorem 5.2, Corollary 5.3, Theorem 5.4 and
      Corollary D match the solver's use.
    - The solver's quotation of Corollary 5.3 was a paraphrase in quotation marks, and has been reworded
      as a paraphrase.
  - Takeishi, arXiv:1301.6883v1, **primary source**.
    - Theorem 5.4 gives amenability ⟺ nuclear `C*_r(E)` for some Fell line bundle `E`, with topological
      amenability. So F3 is now verified directly.
    - Theorem 5.3 is Renault's separable reconstruction theorem, with `G` second countable and
      topologically principal.
  - Renault, arXiv:0803.2284v1, primary source.
    - Proposition 4.6 (Kumjian 1.6): `n^*bn(x) = b(α_n(x)) n^*n(x)`.
    - Proposition 4.7(ii): normalizers are supported on bisections.
    - Theorem 5.6: reconstruction.
  - Not re-fetched, standard textbook content: ADR approximately invariant means, CFW / Kechris–Miller in
    Reiter form, Lusin–Novikov, Lyapunov.
    - The CFW form used is the usual one (a μ-amenable CBER is μ-hyperfinite, for any Borel probability
      measure).
    - WebSearch was exhausted for this session as well, so the 2025–26 novelty scan is still undone.
      Priority is unverified and the node claims none.
- **Duplicates.**
  - `bin/cairn search --similar` and a lexical search for "relative uniform Gamma" found no duplicate.
  - The nearest nodes are `uniform-gamma-on-finite-dim-boundaries`, which is absolute Γ and not a
    duplicate, and the XLIX root, which is distinguished in `distinct_from`.
  - The claim id has 55 characters.

**Changed.**
- Artifact.
  - The Corollary 5.3 quotation is replaced by an accurate paraphrase of the hypotheses of Corollary 5.3(ii)
    and Theorem 5.2.
  - Verified theorem numbers and quotations are added for F1, F2 and F3.
  - The trust boundary is updated. The measurewise-amenability fallback is no longer needed.
- Claim.
  - The file said Remark 1 "shows" local relative Γ. It now says the remark only sketches it, and that the
    sketch is not part of the claim.
  - The `T(A) = ∅` and `M_d` cases are stated.
- Route: a line listing the referee-verified citations.

**Verdict.**
- The theorem and its `requires: []` proof are sound as written, modulo textbook imports cited accurately.
- The claim is landed with small fixes.
- Remark 1 (local relative Γ), approach C (tensor products) and approach E remain sketches or dead ends in
  prose only. None of them is a node.
- XLIX itself remains OPEN.
