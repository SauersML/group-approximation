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
