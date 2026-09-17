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
- **Density of Cayley graphs.** Amenability is equivalent to finite subgraphs of density
  arbitrarily close to `2m`. The best known is density `> 3.5` for `{x_0, x_1}` (Guba,
  arXiv:2210.12304, improving Belk--Brown's `3.5`), with sets of size about
  `2^27200` (survey §2). Dies: each improvement removes a local fragment of positive
  density from Belk--Brown forest sets. No family approaching density 4 is known, and
  `thompson-f-folner-function-exceeds-every-tower` forces tower-size sets.
- **Ramsey reformulation.** J. T. Moore, *Amenability and Ramsey theory*, Fund.
  Math. 220 (2013) 263–280, reformulates amenability as a structural Ramsey
  statement that "constitutes a considerable weakening of the Følner criterion"
  (abstract). Neither the precise statement for `F` nor the status of Moore's
  nonassociative Hindman program (arXiv:1209.2063) has been read into this graph.
  Dies here for lack of a verified statement, not for a mathematical reason.
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
- **Small-doubling witnesses for `P_(2,2)` in the positive monoid (2026-09-17,
  swarm-0917-w5-f-folner-numerics).**
  - *Bounded-width families.* `thompson-f-monomial-doubling-width-bounds-degree` covers every
    homogeneous `Y ⊆ M` whose letters are `<= L`, of any degree and size. For such `Y`,
    `|S Y| >= Λ_S(min(D, L-1)) |Y|`.
    - *Invariant:* width `min(degree, largest letter - 1)`.
    - *Where every member dies:* once the degree reaches `L`, splitting by the last letter
      makes the images disjoint translates of degree-`(D-1)` images. So degree adds nothing.
    - With the exact table `Λ_(S_(3,5))(n) > 2.66` for `n <= 12`, a certificate needs a
      component of degree `>= 13` using a letter `>= 14`.
    - The sharper threshold `L - 3` (letters `>= 16`) holds on all computed grids and is
      open: `thompson-f-monomial-doubling-ratio-depends-only-on-width`.
  - *One-letter reduction.* `thompson-f-guba-set-expansion-bounded-by-one-letter-set`
    proves `|S_(3,5) Y| <= 3|X_3 Y| - 2|Y|`. So any `Y` with `|X_3 Y| < (4/3)|Y|` solves
    `P_(2,2)`.
    - Conversely, doubling of `S_(3,5)` forces the Cheeger bound `|X_3 Y| >= (4/3)|Y|`.
    - For `P_(2,1)`, `Λ_(S_(2,4)) = 2Λ_(X_2) - 1` exactly in degrees `<= 10`.
  - Not decided: whether the increments `0.113, 0.091, 0.074, 0.064, 0.055` of
    `Λ_(S_(3,5))` in degrees 8–12 level off above 2. Geometric and power-law fits disagree.
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
