---
rg: 2
id: thompson-f-is-amenable
kind: claim
title: Thompson's group F is amenable
root: true
distinct_from:
  thompson-f-is-not-amenable: that is the opposite answer to the same named problem; this is the amenable answer, which would force the Følner function of F to outgrow every fixed tower of exponentials.
  thompson-v-hyperlinear: that asks whether V embeds into a tracial matrix ultraproduct; this asks whether the subgroup F of V admits Følner sets, a strictly stronger approximation property for F.
---

**OPEN.** Richard Thompson's group `F` is amenable. `F` is the group of
orientation-preserving piecewise-linear homeomorphisms of `[0,1]` with finitely
many breakpoints, all at dyadic rationals, and slopes powers of 2.

*Marked `root` because it answers a named open problem.* Survey of the current
state: V. Guba, *Amenability problem for Thompson's group F: state of the art*,
arXiv:2305.07113v4 (19 Oct 2023), J. Groups Complexity Cryptology 15 (2023).
The two answers are recorded as two roots: this one and `thompson-f-is-not-amenable`.

Unconditional constraints in this graph:
- `thompson-f-has-no-free-subgroups`: `F` has no free subgroups and is not
  elementary amenable, so neither answer follows from a classical criterion.
- `thompson-f-folner-function-exceeds-every-tower`: a `C^-n`-Følner set has at
  least `exp_n(0)` elements.
- `thompson-f-random-walks-are-not-liouville`: finitely supported non-degenerate
  random walks have non-trivial Poisson boundary.
- `thompson-f-is-not-strongly-amenable`.
- `thompson-f-amenable-iff-group-ring-is-ore`: amenability is the Ore condition
  for `K[F]`.

Source map: `research/artifacts/thompson-f-amenability-map-2026-09-12.md`.

## Attempts

- **Explicit Følner families.** Any construction has to beat
  `thompson-f-folner-function-exceeds-every-tower`. A family whose size is
  bounded by a fixed tower `exp_k` in `1/epsilon` cannot be Følner for small
  `epsilon`. Balls and bounded-depth forest-diagram families have elementary
  growth. Dies: every explicit family of bounded recursive complexity is excluded,
  so a witness must come from a non-elementary recursion or a non-constructive
  argument.
- **Liouville measures.** By the Kaimanovich–Vershik and Rosenblatt criterion,
  amenability is equivalent to the existence of a non-degenerate symmetric
  measure with trivial Poisson boundary.
  `thompson-f-random-walks-are-not-liouville` excludes every strictly
  non-degenerate finitely supported measure.
  `thompson-f-finite-breakpoint-moment-walks-are-not-liouville` (swarm-0917,
  obstruction-miner) extends the kill to every `µ` with `sgr supp µ = F` and
  `E_µ|Br(h)| < ∞`, hence every finite-first-moment measure. This is the extension
  Kaimanovich expected in 1602.02971 §7.A.
  - *Invariant:* the breakpoint-cocycle lamp configuration `c(g_n) ∈ Z^D`.
  - *Where every member dies:* the dyadic quotient walk is transient and doubly
    stochastic (`thompson-f-dyadic-orbit-walks-are-transient`), so the expected flip
    count is at most `G(z,z) E_µ|Br|`. The lamps stabilize, and an element fixing
    `1/2` with a breakpoint there turns the law of the stabilized lamp into a
    nonconstant harmonic function.
  - Dies: surviving witnesses have infinite Green-weighted breakpoint count at every
    dyadic point. The next rung, finite entropy, is open. Killing it would still not
    decide the question, since by [Ers04b] some amenable groups have no
    finite-entropy Liouville measure.
  - *2026-09-17, finite-entropy rung (swarm-0917-w5-f-l2-proper).* The rung is now the OPEN claim
    `thompson-f-finite-entropy-walks-are-not-liouville`, split into two parts that can each fail.
    - Established, `thompson-f-interval-avoiding-walks-have-positive-entropy`: suppose the induced dyadic chain from
      some `x` avoids some `[x,y]` with positive probability. Conjugated `x_0`-bumps inserted as `Δ`-letters are then
      readable at uncovered support endpoints, so the entropy is positive.
    - Open: avoidance itself. Its negation is forced on any finite-entropy Liouville witness, whose transient induced
      chain must a.s. approach every dyadic from the right.
    - Dies at: real-topology accumulation of the induced chain, which transience does not control.
- **Group-ring equations.** By `thompson-f-amenable-iff-group-ring-is-ore`,
  amenability is the Ore condition for `K[F]`: every pair of nonzero `a, b` has a
  nonzero common multiple. Guba's survey (arXiv:2305.07113, §3, read in full) reduces
  this to homogeneous pairs in the positive monoid, Problems `P_(d,m)`. It solves
  `P_(1,m)` for all `m` and `P_(2,1)`. This graph adds:
  - all pairs `(1 - a, 1 - c)` (`thompson-f-binomial-pairs-have-common-multiples`);
  - all pairs `(1 - h, b)` with `h` conjugate to `x_0^{+-1}`, `x_1^{+-1}` or
    `(x_1 x_0^-1)^{+-1}` (`thompson-f-one-minus-x0-is-ore-with-every-element`,
    `thompson-f-one-minus-x1-is-ore-with-every-element`);
  - every twisted binomial `1 + lambda g` with `g` one-bump, against every element
    (`thompson-f-one-bump-binomials-have-common-multiples`); with `g` multi-bump, against
    elements of `K[H_i × Z_i]` (`thompson-f-multibump-binomials-meet-stabilizer-ideals`)
    and, when the bump endpoints are dyadic, against elements of the pointwise stabilizer
    of the bump endpoints (`thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals`,
    2026-09-13, unreviewed).

  The whole binomial side is the open claim
  `thompson-f-every-twisted-binomial-is-ore-with-every-element`. It dies at multi-bump
  binomials against elements that move bump endpoints: no common multiple of such a family
  lies in the group ring of a point stabilizer, so the one-bump nesting argument cannot run.
  Dies at `P_(2,2)`: the survey's cardinality method needs a set with `|S Y| < 2|Y|`
  for the nine degree-two monomials `S`, and none is known. Unit-coefficient
  multiples fail outright: `Z_+[M]` is not Ore (survey Theorem 3.6).
  2026-09-17, compute scout, OPEN: `thompson-f-p22-cylinder-functional-needs-thin-skeletons`.
  - The doubling ratio `h(S)` is the infimum of an exactly computable functional on cylinder
    partitions of the critical Boltzmann local limit.
  - The best value found is `h(S_(3,5)) <= 20143/8698 ≈ 2.3158` (3802 cells), below the degree-12
    exact value 2.6676 but still far from 2.
  - Dies at the refinement strategy. Generic refinement gains only about 0.04 per 24-fold increase in
    cells, and for `X_1` it stays near 1.2 while vine partitions with 4228 cells reach `103/100`. A
    certificate needs a guessed thin skeleton for `S_(3,5)`.
- **Common multiples with controlled radius.** (swarm-0917, obstruction-miner.)
  `ore-radius-function-bounds-folner-radius` localizes Bartholdi's garden-of-Eden automaton
  (arXiv:1605.09133v2, §2) and solves its `(r-1) × r` matrix, `r = H_n n! + 1`, `n = |B(k)|`, by Ore
  column elimination. The support of the kernel vector has `|B(k)F| < (1 + ln n)|F|` inside the ball
  of radius `τ^(r-1)(k)`, where `τ(R) = R + Ω(R)` and `Ω` is the Ore radius function.
  `thompson-f-ore-radius-function-is-not-quasi-polynomial` combines this with Moore.
  - *Invariant:* the Ore radius function `Ω_K` of `K[F]` against Moore's tower.
  - *Where every member dies:* any scheme giving common multiples of radius at most
    `exp_j((log_j R)^c)` for all pairs supported in `B(R)` dies at the elimination-plus-Bartholdi step.
    This covers polynomial or quasi-polynomial identities and linear algebra in polynomial degree, for
    every field. The step produces an `O(log k / k)`-Følner set of size at most `exp_(j+5)(3k+2)`,
    against Moore's tower of height about `log_C k`.
  - The pair-level shortcut is false. In `Z^d` the common multiple `t = b`, `u = a` of two elements
    supported on the simplex has doubling `(d+2)/2`.
  - Exponential control `Ω(R) <= 2^R` is not excluded, since the factorial elimination depth
    exceeds the available tower height. Surviving witnesses must use common multiples whose radius
    is not bounded by any fixed `exp_j((log_j R)^c)`.
- **Density of Cayley graphs.** Amenability is equivalent to finite subgraphs of density
  arbitrarily close to `2m`. The best known is density `> 3.5` for `{x_0, x_1}` (Guba,
  arXiv:2210.12304, improving Belk--Brown's `3.5`), with sets of size about
  `2^27200` (survey §2). Dies: each improvement removes a local fragment of positive
  density from Belk--Brown forest sets. No family approaching density 4 is known, and
  `thompson-f-folner-function-exceeds-every-tower` forces tower-size sets.
- **Ramsey reformulation.** J. T. Moore, *Amenability and Ramsey theory*, Fund.
  Math. 220 (2013) 263–280, reformulates amenability as a structural Ramsey
  statement that "constitutes a considerable weakening of the Følner criterion"
  (abstract).
  - *2026-09-17 (swarm-0917-w6b-w6b-f-break, logic-computability).* The statement is now read in:
    `moore-ramsey-criterion-for-amenability` (ESTABLISHED by citation). It gives Theorem 1.3 and Towsner's bound
    `Føl_S(k) ≤ 5^{R^{2p}(1)}` for `(3/4)^p < 1/(4k)`.
  - *Quantitative transfer.* `thompson-f-ramsey-function-iterates-reach-towers` (ESTABLISHED, unreviewed).
    - `R^{j_n}(1) ≥ exp_{n−1}(0)/log₂5` with `j_n = O(n)`.
    - So no bound `R(m) ≤ exp_q((log_q m)^d)` holds. That kills every quasi-polynomial "moderate rate" in Moore's
      Section 7 hope.
    - The known inference cannot exclude an elementary `R_F`, because `exp_r` satisfies all its constraints.
  - *Fork.* If AMP(D) holds for some `D`, then `R_F` is not elementary. The Ramsey route is then pinned to the
    Følner tower like every other route.
    - The surviving branch is the OPEN claim `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`
      (¬AMP). It is necessary for an elementary `R_F`, and it implies the root through the route
      `thompson-f-amenable-via-costly-ramsey-amplification`.
    - *Invariant:* `log* R^j(1)`, which grows linearly in `j`.
    - *Where every member dies:* the nested-Ramsey recursion (3⇒4) of Moore's Theorem 2.1. It composes `R`
      `Θ(log 1/ε)` times, so any transfer through nested Ramsey sets loses exactly one iteration level.
  - *Nonassociative Hindman program.* `free-magma-carries-an-idempotent-finitely-additive-measure` (OPEN), wired to
    the root by the route `thompson-f-amenable-via-idempotent-magma-measure`.
    - The existence proof in arXiv:1209.2063 is withdrawn, with an error in Lemma 4.13.
    - Theorem 3.3 (an idempotent measure gives an invariant mean) re-checks.
    - Dead classes: ultrafilters, killed by a parity homomorphism, and finite-quotient obstructions to existence,
      killed by Brouwer on the simplex.
  - Dies: at AMP for the moderate-rate route, and at Lemma 4.13 for the idempotent-measure route.
- **Strong amenability.** `thompson-f-is-not-strongly-amenable`: `F` has a
  proximal action without fixed points, so no argument through strong
  amenability can work.
- **This graph's compression rigidity.** `F` lies in `V`, which has the Haagerup
  property (`thompson-v-has-haagerup-property`, whose source covers `F`), so by
  `a-t-menable-groups-have-no-rigid-compression-defect` `F` carries no rigid
  compression defect. Those tools decide soficity questions for Kazhdan pairs.
  Dead for amenability in both directions.
- **Recurrence plus amenable stabilizers, and building F from F-free groups.**
  The Juschenko–Nekrashevych–de la Salle route: find a recurrent action, which is
  extensively amenable, and prove the stabilizers amenable.
  - `thompson-f-recurrent-orbits-have-stabilizers-containing-f`: in any finitely
    generated host `G ⊇ F` (F, T, V, full groups, automaton groups), every recurrent
    orbit has `G_x ∩ F` containing a copy of `F`. The proof is a rank-three test
    (`recurrent-orbits-force-every-z3-to-meet-the-stabilizer`: a free `Z^3`-orbit
    roughly embeds, so it is transient) plus Brin ubiquity.
  - `f-free-groups-are-closed-under-recurrent-extensions`: groups with no copy of `F`,
    and groups with no section `F`, are closed under extensions, directed unions and
    recurrent extensions (with quotients too, for section-closed bases). So `F` is not
    in the closure of residually finite, LEF or locally subexponential groups under
    these operations.
  - *Invariant:* containing a copy of `F`.
  - Dies: at the stabilizer step, whose input "`G_x` amenable" already includes
    amenability of `F`. Not covered: extensive amenability proved without recurrence
    (`f-dyadic-ea-iff-inverted-orbit-confinement`), germ-groupoid variants, and analytic
    routes. (swarm-0917, obstructor.)
- **Uniform stability, asymptotic cohomology and separable bounded cohomology.**
  `lamplighter-closure-invariants-cannot-decide-f-amenability`. Let `LC` be the smallest class
  containing every `G ≀ Z` and closed under quotients by amenable normal subgroups and under
  coamenable overgroups. `LC` contains every amenable group, the non-amenable `F_2 ≀ Z`, `F'` and
  `F`. For `F` the chain is `Γ_0 ≀ Z → ⟨Γ_0, g⟩ ≤ F' ≤ F`, following the Fournier-Facio–Rangarajan
  proof.
  - *Status:* the barrier node is OPEN. Items 1 to 4 and every individual kill below are proved,
    but a referee found the completeness sentence unsupported: the imports cover only
    submultiplicative norms, while the normalized Hilbert--Schmidt norm and normalized Hamming
    distance are finite-dimensional targets using the same sup over pairs that are not
    submultiplicative. That gap is parked as
    `lamplighter-closure-covers-normalized-nonsubmult-targets`.
  - *Invariant:* satisfying the three closure axioms. Uniform `U_f`-stability with a linear
    estimate does, for every submultiplicative norm.
  - Dies: the Kazhdan contrapositive, and `U(1)`/quasimorphism instability witnesses, die at "`F`
    is unstable": every uniform asymptotic homomorphism of `F` is close to one through `Z^2`. The
    converse "stable implies amenable" dies at `F_2 ≀ Z`, `T` and `V`.
  - Finitary asymptotic-cohomology vanishing holds on `F'` and on `F_2 ≀ Z`.
  - Monod's separable-coefficient bounded acyclicity holds on `F`, on all `G ≀ Z` and on amenable
    groups.
  - Uniform non-approximability of `F` is shared with the amenable group `S_3 ≀ Z`.
  - Not covered: pointwise relator stability (`thompson-f-relator-system-stable-in-permutations`),
    strong Ulam stability on infinite-dimensional `U(H)` (which breaks the lamplighter axiom at
    `F_2 ≀ Z`), Johnson-type non-separable coefficients, and — the referee's addition — uniform
    stability for normalized non-submultiplicative finite-dimensional targets. (swarm-0917,
    e-f-transplant, stability-approximation.)
- **Juschenko–Monod twisted embeddings: extensive amenability plus a functor cocycle
  with amenable kernel** (JMBMdlS arXiv:1503.04977, corollary and remark in §1).
  - *Germ-groupoid variant with recurrence.* `thompson-f-point-orbits-are-transient`
    shows that every orbit of `F` on `(0,1)` or on the Cantor set is transient. The proof
    plants the deep part of the dyadic graph in each tail class. So the recurrence
    criterion for extensive amenability never applies to singular sets of the
    interval model.
  - *Functor cocycles on unfaithful actions.* In
    `f-functor-cocycles-need-an-exotic-recurrent-action`, suppose a nontrivial normal
    subgroup of `F` acts trivially on `X`. On it the cocycle is a homomorphism whose
    kernel is normal in `F`. By the normal-subgroup import, `F` then lies either in
    `ker c` or in a quotient of some functor value `𝔉(A)`.
  - *Invariant:* a section isomorphic to `F`.
  - Dies: at the kernel step or at the functor step. With recurrence as the engine, a
    surviving member needs an exotic recurrent `F`-set, one whose stabilizer does not
    contain `F′`. Such a stabilizer contains no end-rigid subgroup and fixes no interior
    point. Whether one exists is `thompson-f-recurrent-f-sets-factor-through-the-abelianization`
    (OPEN).
  - Not covered: faithful actions made extensively amenable by non-recurrent means. On
    the dyadic orbit `D`, the breakpoint cocycle `c_g(t) = log_2 (h′(t⁺)/h′(t⁻))` with
    `h = g⁻¹` takes values in `Z^(D)`, and its kernel is trivial. So extensive
    amenability of `F ↷ D` already gives the flagship through the corollary, and this
    case is the flagship itself. (swarm-0917-w4-f-extensive.)
- **Sandwich splits and their kernel trichotomy (swarm-0917-w5-f-decomp, 2026-09-17).** This covers splits
  `A ⇐ P ∧ Amen(K)`. They come from twisted embeddings, with `P = EA(X)` and `K = ker c`, faithful or not, and
  recurrent or not. They also come from co-amenable induction, with `P = Coam(K)`.
  - `f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic` (ESTABLISHED) shows `A ⟺ P ∧ Amen(K)`.
  - If `K` contains `F`, then `Amen(K) ⟺ A`.
  - If `K` is amenable, then `P ⟺ A`.
  - *Invariant:* the Brin–Sapir type of the kernel.
  - *Where every member dies:* at the kernel step or the action step. It survives only when `K` is F-free and
    not elementary amenable, which refutes the Brin–Sapir conjecture.
  - In the co-amenable case such a `K` is unconfined, and its coset means are mean-free, so `F` is sofic.
  - The one uncollapsed split is recorded as the route `thompson-f-amenable-via-exotic-co-amenable-subgroup`.
    Its prerequisites fail independently: `f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f` fails
    under Brin–Sapir, and `every-f-free-subgroup-of-thompson-f-is-amenable` fails only if `F` is non-amenable.
  - Attacks on both are recorded under their Attempts. P2 reduces to the Brin–Sapir germ-kernel descent with
    "EA" replaced by "amenable", and dies at the same step.
- **Gaussian / cnd certificates, Haagerup-to-amenable (swarm-0917-w5-pull-f-1, 2026-09-17).** This covers
  proving amenability through a conditionally negative definite `psi` on `F` with finite balls and
  `log|{psi <= R}| = o(R)`. The deformation `e^{-t psi}` in `l^2` then gives amenability via
  `cnd-ball-growth-bounds-return-probability-for-every-group`, and it is the natural transplant of
  Farley's and Brothier–Jones' cocycles.
  - *Invariant:* the ψ-ball growth profile.
  - *Where every member dies:* `thompson-f-cnd-certificates-need-near-exponential-ball-growth` (ESTABLISHED,
    unrefereed). The Markov-type-2 bound `E psi(X_n) <= n E_mu psi` gives `p_{2n} >= 1/(4|B_{2cn}|)`.
    Følner level sets of the lazy walk plus Moore's theorem give
    `p_{2N} <= exp(-N C^{-2(1+l(N log_2(|Γ|+1)))}/16|Γ|^2)`. Together they force
    `log|B_R| >= κ R C^{-2 log* R} - log 4`.
  - *Consequence:* every profile `R/g(R)` with `log g / log* R -> inf` is excluded. That includes polynomial,
    `exp(R/log R)`, and `exp(R/log^{(k)} R)`.
  - *Survivors:* profiles exponential up to a factor `C^{O(log* R)}` in the exponent. This is the same band
    as the Følner tower.
  - *Also:* Theorem A there is an unconditional upper bound on the return probabilities of `F`, of
    exponential type at every computable length.
- **Liouville measures for actions, both directions (swarm-0917-w7-w7-f-follow, 2026-09-17, probability-random).**
  - *Established:*
    - `amenably-coupled-actions-admit-symmetric-liouville-measures`. Every transitive action in which each finite
      set lies in one orbit of an amenable subgroup (LAT) has a non-degenerate symmetric Liouville measure. It
      covers every orbit of `F` in `(0,1)` (via a chain element `f` with `f(t_i) = t_{i+1}`), `T ↷ D/Z`, and every
      lamplighter action.
    - `juschenko-zheng-question-5-fails-for-countable-groups`. `SL_2(R_alg) = BK`, with abelian stabilizers.
    - `liouville-action-criteria-cannot-decide-thompson-f-amenability`, the class kill.
    - The import `juschenko-zheng-liouville-actions`.
  - *Invariant:* LAT.
  - *Dies at:*
    - Kaimanovich's criterion ("find an action with no Liouville measure") dies at "exhibit the action". LAT
      actions are always Liouville. Non-LAT `F`-sets exist only if `F` is nonamenable, and they certify it with no
      boundary theory. On the regular action the criterion is the root.
    - The positive direction dies at "Liouville ⟹ amenable". `T ↷ D/Z` is a counterexample, and so are
      `P_f(F_2) ⋊ F_2` and `SL_2(R_alg)`. Also `F ↷ D` and its lamplighter action are Liouville unconditionally.
  - *Survives, open:* the group-level Liouville program, and Juschenko–Zheng's Question 5 for finitely generated
    groups together with a LAT `F`-set with abelian stabilizers, which would follow from `F = HK`, `H` amenable,
    `K` abelian.
- **2026-09-18 (swarm-0917-w8-w8-f-pull), abelian factorizations `F = HK` (obstruction-miner, host-geometry).**
  This attacks the factorization survivor of the previous entry.
  - *Established (unrefereed):* `thompson-f-abelian-cofactors-fixing-an-interval-force-f-into-h`. If `F = HK`
    with `K` abelian, then:
    - either `H` contains a copy of `F`, or `F` acts faithfully on `F/H ≅ K` with `C_F(K)` acting by translations;
    - if `K` fixes an open interval pointwise, then `H ⊇ F(a,b) ⊇` a copy of `F`.
    So `H` amenable forces `F` amenable, and the route is circular.
  - *Invariant:* a copy of `F` in the cofactor. *Dies at:* proving `H` amenable.
  - *Open, reduced:* the general case, `thompson-f-abelian-factorizations-put-f-into-the-cofactor`. This includes
    dense-support `K` such as `⟨x_0⟩`.
    - Lemma A and an orbital reduction show that it follows from a negative answer to problem (SA): no transitive
      action of `F ≀ Z` on `Z` with the top generator as shift and no point stabilizer of the base factor containing
      a copy of `F`.
    - Proved constraints on a counterexample: the base factor acts faithfully, and the base group does not act freely.
- **Juschenko–Zheng Question 5 through T = F·R_D (swarm-0917-w8-w8-f-last1, 2026-09-18, reframing).**
  - *Established:* `jz-question-5-for-thompson-t-implies-f-nonamenable`. Every `g ∈ T` is uniquely
    `g = fρ` with `f ∈ F` and `ρ` the dyadic rotation `ρ_{−g⁻¹(0)}`. So `F` acts simply transitively on
    `X = T/R_D`, whose stabilizers are conjugates of the Prüfer 2-group `R_D`. If `F` is amenable, `T ↷ X` is
    LAT, hence symmetric-Liouville, and `T` (finitely presented, nonamenable) answers Question 5 negatively.
  - *Invariant:* the exact factorization `T = F·R_D` with `R_D` abelian.
  - *Dies at:* the w7 survivor's step "assume Question 5 for finitely generated groups". Applied to `T` it
    already proves `F` nonamenable, so that hypothesis contradicts the conclusion it was meant to serve. The same
    holds for any "Liouville + stabilizers in `𝒮` ⟹ amenable" criterion for finitely generated groups with
    `𝒮 ∋ R_D`, and for amenable stabilizers directly via `T ↷ D/Z`. No Liouville-action route to this root
    survives.
  - *Consequence:* this root implies that Question 5 fails for finitely presented groups, as Juschenko and
    Zheng expect.
  - *Spawned:* `thompson-f-not-amenable-via-rotation-cosets-of-thompson-t`, which targets the negation, with the OPEN
    prerequisite `thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive` (some finite `S ⊆ F` has no
    dyadic-rotation twist generating an amenable subgroup of `T`). If that fails, Question 5 fails for `T`
    unconditionally.
- **Cube-complex boundary routes (swarm-0917-w9-w9-f-pull, 2026-09-18, host-geometry, obstruction-miner).**
  - *Established:* `stein-farley-height-fixes-a-roller-boundary-point`.
    - The Farley CAT(0) cube complex `X_F`, the space of `F`'s proper cubical action, is graded by height.
      Every edge raises the height by 1, and upward expansions are directed.
    - So the upper halfspaces of the expansion hyperplanes form a non-principal ultrafilter `σ_F ∈ ∂X_F`
      fixed by `F`, whose horofunction is the height. `F` acts simply transitively on each horosphere.
  - *Invariant:* `σ_F`, the up-orientation of the expansion hyperplanes.
  - *Class killed, and where it dies:*
    - Amenability of `F`, or its exactness (property A), via a topologically or Zimmer amenable action on
      `X̄_F`, `∂X_F`, or any compact `F`-space with an `F`-fixed point, is root-equivalent. The approximately
      equivariant maps evaluated at `σ_F` are already a Reiter sequence, and quantitatively the support radius
      is at least `log` of Moore's tower.
    - For the opposite direction, the Roller-boundary Tits-alternative and Poisson-boundary tools need no finite
      orbit in `X̄`, and `F` has one.
  - *Calibration:* `V` acts on its own graded Farley complex with a fixed Roller point and transitive horosphere
    actions (stabilizers `S_n`), yet contains `F_2`. So the fixed-point data are neutral. Any cube-complex proof
    must use the planarity of forest diagrams, the one thing that separates `F` from `V`.
  - *Not decided:* whether `X_F` has property A as a metric space. If it does, `F` is exact. That is the only
    surviving cubical route to exactness, and it is not a route to amenability.
- **Proof strength: elementary arithmetic (swarm-0917-w10-w10-f-pull, 2026-09-18, quantifier-shift, obstruction-miner).**
  `thompson-f-amenability-unprovable-in-elementary-arithmetic` is ESTABLISHED (unrefereed). It is
  unconditional: `IΔ0 + Exp + Th_Π1(N)` does not prove the Π2 Følner sentence `∀n ∃A (A is c^-n-Følner)`, nor any
  sentence that elementarily implies it. The same holds for `EA`.
  - *Class killed:* every argument whose Π2 content lives in elementary arithmetic. It may be non-constructive
    (counting, pigeonhole, averaging, probabilistic existence, case splits) and may use arbitrary true Π1 facts.
    This sharpens "Explicit Følner families" from families of bounded complexity to proofs of bounded strength.
  - *Invariant:* the growth of the Følner search `g_Γ`, compared with the provably recursive functions
    (`ea-provably-recursive-functions-are-kalmar-elementary`, Henk–Pakhomov verbatim).
  - *Where every member dies:* witness extraction. The finitely many Π1 axioms are absorbed into the search.
    Then `g_Γ` is Kalmár elementary, so `g_Γ <= exp_(k+1)`, against Moore's `|A| >= exp_n(0)`.
  - *Calibration:* Brieussel–Zheng `Δ_U` with `U = exp_n(0)` is amenable, and its Følner sentence is equally
    unprovable. So the kill measures Følner growth only, not amenability.
  - *Gates:* the Ore form (Bartholdi elimination iterates `τ` factorially) and Moore's Ramsey form (Towsner's bound
    iterates `R` `Θ(log 1/ε)` times). Both escape, since an elementary witness there gives only a tower Følner bound.
    These are the graph's two recorded survivors: exponential Ore radius and elementary `R_F`.
  - *Next rung (open):* `IΣ1`, `PRA` and `WKL0` prove every tower total. Killing them needs a
    non-primitive-recursive lower bound on the Følner function of `F`.
- **Hyperbolic-boundary routes (swarm-0917-w10-w10-f-break, 2026-09-18, belief-breaker, class kill).**
  - *Established (unrefereed):* `thompson-f-hyperbolic-actions-have-a-finite-boundary-orbit`, modulo the quoted DSU
    classification. Let `F` act isometrically, with unbounded orbits, on any Gromov-hyperbolic metric space, proper
    or not.
    - There is an orbit `F·ξ ⊆ ∂X` of size at most 2, fixed pointwise by some `F_0 ⊇ F'` of index at most 2. The
      action is parabolic, focal or lineal; general type would give a free subgroup.
    - The Busemann pseudocharacter at `ξ` is a homomorphism `ℓ: F_0 → R` with `ℓ(F') = 0`, proved by a swindle
      pushed by `h^2`. It equals `−log` of the boundary derivative. So `k` is loxodromic iff `k ∈ F_0` and
      `ℓ(k) ≠ 0`, and no element of `F'` is ever loxodromic.
  - *Invariant:* the finite boundary orbit, forced by `thompson-f-has-no-free-subgroups` alone.
  - *Class killed, and where it dies:* amenability or exactness of `F` via a topologically amenable action on any
    compact `F`-space receiving an equivariant map from `∂X`, or via a Zimmer amenable action with an atom on
    `F·ξ`, is root-equivalent. The step where every member dies is averaging the maps `m_n: Z → Prob(F)` over
    `F·ξ`, which already gives a Reiter sequence. Quantitatively this is the same Moore-tower pin as the Roller
    kill.
  - *Calibration:* Adian's non-amenable Burnside groups have the same invariant. Hyperbolic loxodromy of `F`
    factors through `Z^2`.
  - *Survives:* actions with bounded orbits, and atomless measure classes. Poisson boundaries are always amenable
    and carry no information.
- **Property A of cubical hosts (swarm-0917-w11-w11-f-pull, 2026-09-18, host-geometry, obstruction-miner).**
  This decides the survivor left undecided in the previous entry, and the answer is **no**.
  - *Established:*
    - `nowak-hamming-cubes-have-property-a-arbitrarily-badly`, a citation of Nowak through Willett.
    - `cat0-cube-complexes-with-property-a-are-finite-dimensional`. Every cube of a CAT(0) cube complex is an
      isometric Hamming cube with a 1-Lipschitz gate retraction, so infinite dimension kills property A.
    - `cubical-hosts-of-thompson-f-never-have-property-a`.
  - *Consequence:* `X_F` and `X_V` fail property A. More strongly, every CAT(0) cube complex on which a group
    containing `F` acts with finite vertex stabilizers fails property A. A free cube-permuting action of `F` on
    a finite-dimensional CAT(0) cube complex would give a free resolution of finite length, contradicting
    `cd F = ∞`. Acyclicity comes from Leary's convex hulls.
  - *Invariant:* `cd F = ∞`, together with Nowak's unbounded support radius on the cubes `Q_n`.
  - *Class killed, and where it dies:* "`F` is exact via a metrically proper action on a CAT(0) cube complex
    with property A" dies at "the host has property A", for every host.
  - *Calibration:* the obstruction sees only `cd = ∞`, which the amenable group `⊕_N Z` shares. So it says
    nothing about whether `F` is exact or amenable.
  - *Not decided:* whether `F` is exact through actions with infinite stabilizers, or through non-cubical
    geometry. Nothing about amenability changes.
- **Calibrating Moore's derivative amplification (swarm-0917-w12-w12-f-pull, 2026-09-18, quantifier-shift, obstruction-miner).**
  - *Established:* `marginal-derivative-amplification-is-sharp-at-log-height`.
    - Abstract Moore's mechanism as a derivative datum: a map `∂` equivariant on a good set, with
      a `c`-thin (for example marginal) bad set.
    - Then `μ({h ≥ n}) ≥ μ(S) − bd(μ)(qⁿ−1)/(2|Γ|)` with `q = 1 + 2c|Γ|`. So `ε`-Følner forces
      height `⌊log_q(1 + 2|Γ|/ε)⌋`.
    - A partial `F`-set with Moore's generators and a 1-marginal bad set attains height
      `≤ log_c(1/ε) + O(1)`. Bundling derivatives does not change the rate.
  - *Invariant:* the Følner ratio `bd(μ_i)/μ_i(S)` of the successive pushed measures.
  - *Where every member dies:* the restriction step (Moore's Lemma 3.11/5.13). It multiplies the
    ratio by `≍ c`, and the datum shows it really does.
  - *Class killed:* every Følner lower bound built from a derivative with a thin bad set gives
    height `Θ(log 1/ε)`. So Moore's tower is the ceiling of the method, not an artifact of its
    bookkeeping.
  - *Decomposition:*
    - `thompson-f-folner-function-dominates-every-ackermann-level` (non-primitive-recursive
      `Føl_F`, Moore's Question 1.2 for `F`) follows by the route
      `thompson-f-ackermann-folner-via-tree-derivative-hierarchy`.
    - That route needs the OPEN `thompson-f-trees-carry-an-ackermann-derivative-hierarchy`:
      derivatives on `𝒯` with `Ack_k` contraction and thin bad sets.
    - Two natural candidates die at Moore's Lemmas 5.10 and 5.7, because leaf count is additive
      under the regrouping moves.
- **Germ-groupoid recurrence criterion, all hosts (swarm-0917-w13-w13-f-last1, 2026-09-18, reframing).**
  - *Established (conditional on the unrefereed abelian-factor theorem):*
    `thompson-f-recurrent-germ-criteria-return-f-as-an-input`.
    - Let `G ⊇ F_0 ≅ F` be a finitely generated group of homeomorphisms of any space `X`, and `H` any groupoid of
      germs, with every singular orbit recurrent (JNdlS condition (3)).
    - Then `F_0′` fixes every singular orbit pointwise, because recurrent `F`-sets factor through `F/F′`.
    - By simplicity of `F′`, either some germ group `𝒢_v` contains `F_0′ ⊇ F`, or `F_0′ ≤ G ∩ [[H]]`.
  - *Class killed:* JNdlS Theorem 3.1, and hence Theorem 1.1, applied to any host containing `F`. This is the
    "germ-groupoid variants" gap left by the recurrence kill above.
  - *Invariant:* "contains a copy of `F`".
  - *Dies at:* input (1) (`[[H]]` amenable) or input (4) (germ groups amenable). Each is at least as hard as
    this root.
  - *Corollary:* if neither `G ∩ [[H]]` nor any germ group contains `F`, then some singular orbit is
    transient.
  - *Calibration:* `F ↷ [0,1]` with `H` the locally affine germs satisfies (1), (2) and (4), and (3) fails as
    predicted.
  - *Survivor:* extensive amenability without recurrence (JMMS), which for `F ↷ D` is this root.
- **Explicit spectral test vectors (swarm-0917-w13-w13-f-break, 2026-09-18, census-computation).**
  Amenability is `||P|| = 1`, so the approach is to push certified Rayleigh quotients toward 1.
  - *Established:* `thompson-f-norm-bound-from-forest-renewal-test-vector`, `||P|| > 0.9397`.
    - The certificate is one nonnegative product-form vector on pointed-forest windows of `F`.
    - It is evaluated exactly by a renewal recursion, with no moment data.
    - It beats the moment-route optimum `0.9107`.
    - It puts the reduced cogrowth above `2.6088`, outside ERJvR's published estimate `2.53±0.03`.
  - *Belief change:* the numerical case for non-amenability rested on `||P|| ≈ 0.93`, and that support
    is gone. The float optimum of the ansatz family still rises with the tree-size cutoff:
    `0.8777, 0.9118, 0.9290, 0.9400` at `N = 9, 20, 40, 80`.
  - *Invariant:* the bulk-tree size law of the optimiser, with mean `7.45` at `N = 40` and `12.57`
    at `N = 80`.
  - *Dies at:* every finitely supported certificate is strictly below 1. `Kf = 4f` forces `f` to be
    constant on the infinite connected Cayley graph, so no finite certificate can prove amenability.
  - *Survives as a computable proxy (heuristic, OPEN):* whether `sup_N` of the ansatz optimum is `1`,
    that is, whether the optimal tree-size law escapes to infinity.
  - **2026-09-19 (swarm-0917-w14-w14-f-last1, entropy-measure, obstruction).** The proxy is settled
    negatively: `thompson-f-iid-forest-test-vectors-are-bounded-below-one`.
    - Every product-form vector (i.i.d. bulk trees, arbitrary pointer weight, any cutoff `N`) has limiting
      Rayleigh quotient `(b^2+m)/2 <= 1 - 1/1280`.
    - *Invariant:* the Hellinger idempotence gap `H(nu, nu*nu) >= 1/8` of the bulk size law.
    - *Dies at:* the merge move.
    - *Survivors:* test vectors with correlated neighbouring tree sizes.
- **Log-scale forest limit and the product-form cap (swarm-0917-w14-w14-f-break, 2026-09-19,
  belief-breaker, entropy-measure).** This continues the w13 entry above and answers its open proxy.
  - *Established:* `thompson-f-norm-bound-from-log-scale-forest-limit`,
    `||P|| >= 1/2 + sqrt(2)/3 > 0.9714` in closed form and `||P|| > 0.9743` by an exact certificate.
    - Size-only weights reduce the w13 vector's large-window value to
      `Phi(nu, eta)/2 = (BC(nu,eta)^2 + BC(nu*eta, nu))/2` for two tree-size laws.
    - Log-scale size laws turn `Phi` into a continuum functional of two histograms as the cutoff
      `M -> infinity`.
    - The cogrowth rate is `mu > 15.188`.
  - *Belief change:* both published numerical norm estimates are below the certified truth. They are
    HHR's `||A+A^{-1}+B+B^{-1}|| ≈ 3.87` (`0.9675`) and EP-G's `mu ≈ 15.0` (`0.9682`). The certified gap
    to amenability shrinks from `0.0603` to `0.0257`.
  - *Class killed:* `thompson-f-product-forest-vectors-stay-below-71-72`. Every product-form
    forest-stack vector, for any truncation and any positive parameters, has large-window value at
    most `71/72 = 0.98611` (sharper: `0.98596`). The w13 proxy is answered no. The optimal size law
    does escape to infinity, but the family's supremum lies in `(0.9743, 0.9860]`.
  - *Invariant:* the pointer-tree size law `nu` and the tilted bulk size law `eta`, which are
    independent under `|f|^2`.
  - *Dies at:* the merge edge. The merged size `X + Y` of independent sizes exceeds `X` by a fixed
    amount at the median (`P(X+Y <= t) <= F(t-1)G(t-1)`). This forces `TV(nu*eta, nu) >= 1/4 - d/2`
    against `BC(nu,eta)^2 <= 1 - d^2`, where `d` is the Kolmogorov distance.
  - *Survives (OPEN, heuristic):* test vectors that correlate neighbouring tree sizes. A near-eigenvector
    must make the pointer and neighbour sizes comonotone. The necessary condition is
    `P(s <= t < r), P(r <= t < s) = O(sqrt delta)` at quotient `4 - delta`, and it is not written up.
    This is the next family to test.
- **Size-correlated (Markov) test vectors in the log-scale limit (swarm-0917-w14-w14-f-follow, 2026-09-19, census-computation).**
  This follows up the survivor "size-correlated neighbour vectors" of swarm-0917-w14-w14-f-break. The work
  is in `thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit` (OPEN).
  - *Established:* an exact infinite-volume formula for the Rayleigh quotient of stationary Markov size
    chains with recursive shapes. In the formal log-scale limit, merge acts as `max`, so every product
    law gives `2√2/3` exactly. There are necessary conditions for `B → 1`: rows must agree along up- and
    down-steps, and `U + D → 1`.
  - *Belief change (numerical):* order-1 and order-2 chains saturate at `B ≈ 0.954–0.955`, that is
    `R ≈ 0.977`. Bin refinement converges geometrically and memory adds about `0.001`. At computable
    sizes (lifted kernels up to `M = 10⁵`) they stay below the lifted product and far below `0.9743`.
  - *Dies at:* a rigorous ceiling. That needs quantitative rigidity: near-agreement of rows forces a
    near-product chain.
  - *Survivor:* hierarchical or hidden-state laws that encode several log-scales at once. These are the
    Følner-type candidates suggested by Moore's tower bound.
- **Guba's systems Q_k through density (swarm-0917-w15-w15-f-break, 2026-09-19, belief-breaker, group-rings).**
  - *Established (unrefereed):* `thompson-f-guba-q4-systems-have-common-multiples`.
    - For finite `Z`, `|{1, x_0, x_1} Z| <= (3 - δ(Z)/2)|Z|`, where `δ` is the `{x_0, x_1}` density.
    - The copy `ψ(F) = <x_2 x_0^-1, x_1 x_0^-1>` turns `Z` into `Y = x_0^-1 ψ(Z)` with
      `|AY| = |{1, x_0, x_1} Z|`, where `A = {x_0, x_1, x_2}`.
    - A dimension count then solves Guba's `Q_k` for all coefficients and all fields as soon as
      `δ̄ > 4 - 2/k`.
    - Guba's own `δ̄ > 3.5` (survey Theorem 2.7) therefore solves `Q_4`.
  - *Belief changed:* the survey's "possible candidiate to a negative solution" `Q_4` is dead, and so
    is its `ε = 1/4` hope. The graph's listing of `Q_4` as an open non-amenability candidate (in
    `thompson-f-is-not-amenable` and `thompson-f-rescaled-x0-binomials-have-common-multiples`) is
    superseded.
  - *Invariant:* the `{x_0, x_1}` density `δ̄`.
  - *Where every member dies:* a negative `Q_k` forces `δ̄ <= 4 - 2/k`. So the Q-family can certify
    non-amenability only at `k >= 5`, and `Q_5` falls to any finite set of density `> 3.6`. On the
    amenable side, each density improvement solves a further block of `Q_k`. Density approaching 4
    solves them all, but that is the root itself.
  - *Computation:* exact mod-`p` search (`experiments/guba-qk-2026-09-17/qk_linalg.py`) finds no
    solution of `Q_2`, `Q_3` or `Q_4` in degree `<= 5`. The solutions exist only on huge supports.
- **Is the forest-window support lossy? (swarm-0917-w15-w15-f-pull, 2026-09-19, transplanter, operator-algebras.)**
  The w13 test vectors live on the windows `E(S_n)`. The question is whether that support alone
  keeps them below `1`.
  - *Established:* `thompson-f-one-sided-forest-windows-are-norm-lossless`. It is not lossy.
    - The move graph on `S_n` is the induced Cayley subgraph on `E(S_n)`.
    - Its top eigenvalue `rho_n` increases to `4||P||` exactly.
    - So `F` is amenable iff `rho_n -> 4`, and the union of the windows is the positive-monoid
      forest cone `R`.
    - Proof: an intrinsic membership test for `R`, left translates that absorb every finite set
      into `R` (the Ore property, via dyadic refinement), and the compression identity
      `||K_R|| = ||K||`. The steps are checked in exact arithmetic for `n <= 7` and on 200 random
      sets.
  - *Decomposition:* `<f,Kf> = 4 - delta(f) - energy(f)` on `R`. Here `delta(f)` is the `l^2` mass
    on pointer-at-root and pointer-on-leaf states, and `energy(f)` is the Dirichlet energy.
    Amenability is exactly "both can be made small at once".
  - *Dies at:* any ansatz family whose pointer-leaf plus pointer-at-root mass stays `>= c`
    is capped at `||P|| >= 1 - c/4` and cannot reach `1`. This is a checkable necessary condition
    on the w13/w14 families.
  - *Survives:* the w13 proxy, sharpened. The support is exact, so the only open question is
    whether the amplitude class, not the window, can approach `1`. Small exact windows are useless
    as certificates: `rho_12 / 4 ≈ 0.815`, far below the certified `0.9397`.
- **Product forest sets are capped at density 3.5 (swarm-0917-w16-w16-f-break, 2026-09-19, belief-breaker, paradigm/decomposition).**
  The question: can Følner-type sets, 0/1 rather than weighted, come from the w13 product ansatz on
  the lossless windows `E(S_n)`?
  - *Established:* `thompson-f-product-forest-sets-have-density-below-3-5`. The answer is no.
    - A product family has bulk trees `𝒜` (containing the leaf) and pointer trees `ℬ`, with window
      sets `Y_n`. Its density has an exact counting formula, checked against brute-force Cayley
      density for 240 (family, `n`) pairs.
    - In the renewal limit, `δ_∞ <= 3 + 2α^2 < 3.5`, where `α` is the mass of the pointer-size law
      strictly below its median.
    - The depth-`<= k` families give `4 - 2R_k`, which increases to `3.5`. So `3.5` is the exact
      supremum and is never attained.
  - *Invariant:* the tilted size laws `ν` (pointer) and `η` (bulk). In the limit the pointer size is
    independent of its neighbour's size.
  - *Dies at:* the median of `ν`. Merge and shift overlaps are `min`-overlaps, and splitting at the
    median caps them at `αβ + 1/2` and `max(α/β, (1-β)/(1-α))`.
  - *Belief changed:*
    - Belk–Brown's `3.5` is the ceiling of the whole product class, not an artefact of their choice
      of trees.
    - Guba's `3.5004` sets, and any `Q_5` set (density `> 3.6`, via
      `thompson-f-guba-q4-systems-have-common-multiples`), cannot be large product windows.
    - Weighted product vectors reach Rayleigh value `> 3.897` but indicators stop at `3.5`, because
      `min(p, q)` replaces `sqrt(pq)`. The density route to `Q_5` needs non-product sets.
  - *Survivor and open:*
    - Sets where membership of the pointer tree is correlated with its neighbours, including
      two-sided bulk sets.
    - The periodic case where the leaf is not in `𝒜`.
    - Finite windows of product families. The limit proof does not cover them; a float relaxation
      gives `2.00, 2.51, 2.70, 2.80, 2.88` at `n = 4, 8, 12, 16, 20`, still well below `3.5`.
- **Pointer-window subsets of Belk–Brown sets stall at about 3.5006 (swarm-0917-w17-w17-f-break, 2026-09-19, belief-breaker, computation).**
  The question: does the survivor of the product kill beat 3.5 by much? That survivor is pointer
  membership correlated with a window of neighbouring trees.
  - *Recorded (OPEN, numerical):* `thompson-f-belk-brown-pointer-window-subsets-stall-near-3-5006`.
    - In the `n → ∞` local limit, the best window subset of `BB(n, k)` is an exact weighted
      densest-subgraph problem on class windows, solved by min cut.
    - The optimum exceeds `4 − 2R_k` by about `5.9e-4` for every `k` from 10 to 80. The gain does not
      grow with window width or with the number of classes. The limit is about `3.5006`.
    - The optimal removed windows are Guba's `0 K 0 K` special forests, so his `3.5004` is essentially
      this class's optimum.
    - Exact tree types at `k ≤ 2` gain nothing, and the leafless bulk is worse.
  - *Invariant:* the i.i.d. height law of the local limit, with leaf mass `R_k ≥ 1/4`.
  - *Dies at:* the removal criterion. Only leaf/height-`k` alternations have boundary ratio below
    `δ/2`; their ratio is `≥ 3/2` and their mass is `≈ 0.034^j`. `Q_5` (`> 3.6`) is out of reach for
    bounded pointer windows.
  - *Open:* a rigorous uniform-in-width dual certificate; non-local (multi-scale) membership conditions.
- **Near-eigenvectors need log-scale pointer spread (swarm-0917-w20-w20-f-break, 2026-09-20, belief-breaker, probability-random).**
  This proves the "comonotone" survivor condition, which `thompson-f-product-forest-vectors-stay-below-71-72`
  records as a heuristic.
  - *Established:* `thompson-f-near-eigenvectors-need-log-scale-pointer-spread`. Let `f ≥ 0` be a unit
    vector on `R` with Rayleigh value `4 − δ`. Let `s` be the pointer size and `r` the neighbour size.
    Then:
    - `μ(s ≤ t < s+r) ≤ 2√δ`;
    - `μ(r ≤ t < r+s) ≤ 4√δ`;
    - `μ(min(s,r) ≤ 2^J) ≤ 6(J+1)√δ`.

    The proof uses the pointer-right/merge split `<f,Kf> = 2a_0 + 2a_1` and one-sided transport of
    the size law.
  - *Class killed:* every vector, with any amplitudes, whose pointer trees have at most `N` leaves on
    mass `c`. Such a vector has `δ ≥ c^2/(36(⌈log_2 N⌉+1)^2)`.
    - *Invariant:* the law of `log_2 min(s,r)`.
    - *Dies at:* the merge and pointer-right edges, which allow only `6√δ` of crossing mass per
      dyadic scale.
  - *Consequence:* Kesten witnesses have median `log_2 min(s,r) ≥ 1/(12√δ) − 2`. Any certificate that
    reaches `4 − δ` needs truncation `N ≥ 2^{c/√δ}`.
  - *Survivor:* the scale-limit families (log-scale continuum, Markov chains). They satisfy the
    necessary condition, so this caps neither.
