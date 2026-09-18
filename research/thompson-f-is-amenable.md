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
