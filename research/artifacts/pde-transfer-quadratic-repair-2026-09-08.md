# PDE stress-correction transfer: what enters the graph, what was already here,
# and what the same day's Jacobson result removes

Date: 2026-09-08.  Source: an external review note supplied by the user,
extracting transfer candidates from a Navier-Stokes blowup manuscript for the
group-approximation program.  This artifact records the adjudication; the
mathematics that survived it is in the nodes listed in section 3.

No code was run for this record (standing order: no local execution).  Every
number quoted in section 5 is **as reported by the source note** and is not
reproduced here.  The algebra in sections 4 and 6 is proved in place.

## 1. Verdict in one paragraph

One idea transfers with content: use an admissible direction that is *neutral
for the linearization* and pay the residual with its **second-order** term,
instead of asking the linearization to be surjective.  Written out for this
program, the transfer immediately meets an obstruction supplied by the
archive's own established facts: at every compatible Iwahori pair the
first-order-neutral directions are exactly the diagonal coboundaries, those
integrate to curves of compatible pairs, and an integrable direction has zero
projected second-order obstruction.  So the mechanism is empty on the near
sector and can only be attempted where the cohomological description of the
kernel fails.  That is a genuine narrowing of the proposal, not a refutation of
it, and it is what the new nodes record.  The note's second-order step lemma and
its finite-dimensional completion budget are correct and were absent here; they
are landed as established elementary claims.  Its fourth-moment word estimate is
the sharp form of an estimate the archive already uses in a weaker interpolated
form, and it is landed too.

## 2. What the note proposed that this archive already had

| Note item | Already established here |
|---|---|
| Fourth-moment / rank-spike diagnostic for the nonlinear remainder | `normalized-hs-taylor-remainder-is-not-dimension-free` -- stronger: the rank-one spike gives ratio `sqrt(d)`, and it already killed `iwahori-newton-closes-near-sector-proof` |
| Search for second-order escape after first-order neutrality | `research/artifacts/atlas-flip-translation-sector-hessian-screen.md` -- 8,600 exact evaluations with gauge directions excluded, zero directions of negative loss curvature |
| Gauge motions give no corrective curvature | `atlas-phase-jacobian-has-invertible-gauge-kernel`, `atlas-cross-jacobian-cannot-pay-the-gauge-mode` (first-order versions, different problem) |
| Quadratic loss is the admissible rate, linear is not | `quadratic-descent-loss-is-admissible-linear-is-not` (dimension descent, a different iteration) |
| Perfect completeness is a support-face problem | `finite-perfect-strategy-reduces-only-to-support-minimal-irrep`, `extreme-traces-and-local-pruning-do-not-select-fano-caps` -- both sharper than the elementary faithful-state remark |
| Direct sums cannot lower a maximum operator-norm defect | used throughout the Jacobson packet lane; see `jacobson-two-braid-mixed-packet-gap` |
| Fixed-word Lipschitz bound in the padding metric | `flexible-hs-metric-controls-words-and-padding` (with the sharp `A <= A_up <= 2A` conversion the note does not have) |
| Tapered cutoffs | `research/artifacts/tapered-curvature-halo-audit-2026-09-05.md` |

The note is right that these must not be re-announced.  They are cited, not
re-derived.

## 3. What is new here and is now in the graph

- `word-taylor-remainder-has-a-fourth-moment-bound` -- the exact
  `(ell^2/2) max_s ||X_s||_(4,d)^2` remainder bound, the interpolation
  `||X||_4^2 <= ||X||_op ||X||_2` showing it refines the archive's `(NHT1)`,
  and the effective-rank threshold `theta_eff >> e^2` that a correction must
  meet for its nonlinear remainder to be lower order.
- `second-order-step-beats-a-blocked-linearization` -- the conditional
  `e -> O(e^(3/2))` step: a neutral direction of size `O(sqrt e)` whose
  projected quadratic term cancels the blocked component, followed by an
  ordinary linear correction.
- `integrable-neutral-directions-pay-no-second-order` -- the screen: at an
  exact point, a neutral direction tangent to a curve of exact solutions has
  zero projected second-order obstruction.
- `iwahori-second-order-repair-space-is-empty` -- the consequence for
  Dogon-Vigdorovich: `(UIR)` at zero defect says the kernel is the diagonal
  coboundaries, those are integrable, so the projected quadratic form vanishes
  identically on the kernel at every compatible pair.
- `quadratic-repair-steps-complete-in-finite-dimension` -- the completion
  budget: `e -> A e^(3/2)`, movement `B sqrt e`, padding ratio `B e`, closed
  under its own output, imply the iteration stabilizes in one finite matrix
  algebra and gives the modulus `f(x) = min(C sqrt x, 2)`.
- `iwahori-admits-neutral-quadratic-directions` (open) and
  `iwahori-uniform-quadratic-repair-step` (open) -- the two halves of the bet,
  with `iwahori-quadratic-step-from-neutral-directions` and
  `iwahori-flexible-repair-from-quadratic-steps` wiring them to
  `iwahori-local-global-defect-question`.

## 4. The signed covariance correction, proved and parked

Deliberately not a node: it is a lemma with no consumer in this graph today.
Recorded here so a Gram-repair lane can pick it up without re-deriving it.

Let `A` be `m x n` complex with `G = A A^* > 0`, and let `Delta = Delta^*` be
`m x m`.  Put `B = (1/2) Delta G^(-1) A`.  Then

```text
A B^* = (1/2) A A^* G^(-1) Delta = (1/2) Delta,
B A^* = (1/2) Delta G^(-1) A A^* = (1/2) Delta,
B B^* = (1/4) Delta G^(-1) A A^* G^(-1) Delta = (1/4) Delta G^(-1) Delta,
```

so exactly

```text
(A + B)(A + B)^* = G + Delta + (1/4) Delta G^(-1) Delta.
```

If `G >= lambda I` then `||G^(-1) A||^2 = ||G^(-1) A A^* G^(-1)|| = ||G^(-1)||
<= 1/lambda`, hence `||B|| <= ||Delta|| / (2 sqrt lambda)` and
`||B B^*|| <= ||Delta||^2 / (4 lambda)`.  The point is that the *cross* terms
carry a signed correction at linear cost, which a construction starting from
`A = 0` cannot have: there the only available increment is the positive
`B B^*`.

Boundary caveat, which is why this is not a shortcut to perfect completeness.
If `h >= 0` and `rho > 0` is faithful, `Tr(h rho) = 0` gives
`Tr(h^(1/2) rho h^(1/2)) = 0` with a positive argument, so
`rho^(1/2) h^(1/2) = 0` and `h = 0`.  A full-rank interior reserve therefore
cannot be corrected to exact satisfaction of a nonzero positive constraint; the
reserve has to sit inside the correct common support face, which is the actual
problem.  This archive already treats that as the problem: see
`finite-perfect-strategy-reduces-only-to-support-minimal-irrep`.

## 5. The Jacobson recommendation is superseded, on the same day

The note's first recommendation was to run a structure-preserving search on the
12-dimensional mixed packet, parametrizing `H(V) = V H_0 V^*` with
`V in U(pi(K)')` so that the involution and overlap relations stay exact and
only the two braid defects move.  Its reported outcome, unverified here:

| Candidate | first braid | second braid |
|---|---|---|
| supplied packet `H_0` | 1.6693210 | 1.5313202 |
| reported search output | 1.11807 | 0.28514 |

with residual violation of the preserved structural equations about `1e-13`,
two runs agreeing, and the derivative on the 16-dimensional involution-orbit
tangent space of numerical rank 16 (singular values `1.076 ... 3.826`), leaving
about `82.3%` of the stacked residual uncancelled by linear least squares.

That last figure is the note's own honest report that the seed shows **no**
first-order-neutral direction, i.e. exactly the input its quadratic proposal
needs is absent there.

Independently of that, the question the search was aimed at was answered the
same day: `jacobson-two-braid-infimum-is-zero` establishes `gamma = 0` by an
amenable-amalgam countermodel (retain the head `GL_3(F_2)`, only the tail
permutation subgroup and the balanced involution; amalgamate with the full
finite packet over `G_Q x S_(3,P)`; Shulman's amenable-amalgam theorem makes
the amalgam operator-MF and the normal form keeps the packet embedded).  So the
descent the note observed is consistent with the true value, and continuing the
search would decide nothing.  The live question moved to mixed relations with
nonpermutation tail coefficients.

Nothing was written into the Jacobson nodes from here: they were untracked and
under active edit in the shared tree at the time of reading.

## 6. Transfers declined

- **Borel summation / flat residual absorbed into a force.**  A group
  presentation has no freely chosen forcing term; the endpoints (relators
  converging in a corona, versus an exact representation in an admissible
  finite dimension) are not the same endpoint.
- **Spatial oscillation with unbounded derivative.**  For a fixed word,
  `||w(U) - w(V)||_p <= |w| max_s ||U_s - V_s||_p` for `p = 2, inf`, with a
  dimension-free constant (`flexible-hs-metric-controls-words-and-padding`).
  The PDE's `O(1/N)` profile with `O(1)` derivative uses unboundedness of
  differentiation in the profile norm, which has no fixed-presentation
  analogue.  Increasing word complexity would be needed, which changes the
  problem.
- **Averaging / dilution.**  Block-diagonal operator norm is the maximum over
  blocks while normalized HS is a weighted average, so a construction may help
  hyperlinear models and do nothing for MF ones.
- **More trace and moment matching.**  The archive's regular-trace obstruction
  to universal tracial SOS certificates already shows finite moment data cannot
  be the whole instrument, and the exact 12-dimensional Jacobson packet already
  satisfies the marked-rank divisibility while failing both braids.

## 7. What would change the verdict

A single admissible direction, at one pair with defect bounded away from the
compatible locus, that is neutral for the linearization and whose projected
quadratic term has size comparable to the blocked residual.  One such direction
would make `iwahori-admits-neutral-quadratic-directions` a live target rather
than a bet; none is known here, and section 2's Atlas screen is the one place
this archive searched for one and found nothing.
