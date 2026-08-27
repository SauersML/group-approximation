---
rg: 2
id: atlas-wedderburn-hall-deficient-support-certificate
kind: claim
title: Compiled atlas relators force a weighted Hall-deficient Fourier support graph
distinct_from:
  atlas-rectangular-wedderburn-isometry-certificate: that is the singleton-source/single-target special case; this target may use several Fourier corners whose combined target capacity is too small.
  atlas-two-s3-covariance-collapse: that asks for two fixed S3 covariance norms to vanish; this asks for a finite block-support pattern in the full regular-A8 Fourier IR.
  universal-atlas-ideal-cannot-force-hall-deficit: that proves a universal algebraic support certificate is impossible; this target remains open because a finite-multiplicity, coordinate-dependent support reduction need not survive in the exact infinite-multiplicity factor model.
artifacts:
  - experiments/weighted_hall_mincut.py
  - experiments/weighted-hall-smoke.json
---

Use the minimal Wedderburn projections

```text
p_(sigma,a)=e^sigma_aa
```

of the regular `A_8` chart as source and target vertices, with fixed weights

```text
w_(sigma,a)=d_sigma/|A_8|.
```

There is a finite bipartite allowed-edge graph `E`, a source set `S`, and a
constant `gamma>0` such that

```text
sum_(v in S) w_v - sum_(u in N_E(S)) w_u >= gamma,   (AWH1)
```

and the canonical full atlas relator packet forces the total normalized-HS
energy of every forbidden relative-unitary block to vanish:

```text
sum_((v,u) notin E) ||p_u U p_v||_2^2 -> 0           (AWH2)
```

along every zero-defect regular-atlas **finite-matrix** microstate sequence.

This is the finite max-flow/min-cut relaxation of
`atlas-rectangular-wedderburn-isometry-certificate`.  It can exploit several
small target corners at once and is therefore strictly more permissive than
forcing one rectangular block to be an isometry.

## Critical category boundary

`universal-atlas-ideal-cannot-force-hall-deficit` rules out the most obvious
way of proving `(AWH2)`: the forbidden blocks cannot all be universal
algebraic two-sided-ideal consequences of the atlas relator residuals.  The
exact Leavitt group factor contains an internal relative chart unitary with
all relators zero, and the Hall leakage inequality itself remains valid in
that finite tracial factor.  Hence any universal ideal identity producing a
deficient support graph would contradict the exact model.

So `fixed-coefficient-ideal-certificate-controls-hs-defect` remains a valid
proof-system theorem for coefficient consequences, but **an ideal search by
itself cannot close this node at any degree**.  The missing implication must
use information which is genuinely present at finite external multiplicity
and is not an algebraic identity in arbitrary tracial coordinates: ranks,
finite multiplicity dimensions, singular-value selection, coordinate-wise
polar/matching data, or another operation which has no fixed universal lift
to the exact infinite-multiplicity factor model.

## Attempts

- **Do not use bare type incidence.** The archived `S3 -> S4` branching counts
  are exactly Hall-balanced; the general reason is now
  `regular-subgroup-branching-is-hall-balanced`.  The raw four-character comb
  graph is complete and Fourier-flat.  A successful graph must use actual
  finite-multiplicity arrow data, not only subgroup restriction types.
- **Do not search the universal relator ideal for a deficient support graph.**
  `universal-atlas-ideal-cannot-force-hall-deficit` proves that this entire
  certificate class is empty.  The exact ideal backend is still useful for
  local identities which feed a later matrix-specific selection step, but a
  min-cut must not be built by declaring every ideal-certified zero to be a
  globally forbidden edge and hoping for positive deficit.
- **Include an interior separator immediately.** Boundary-only exact models
  survive all first-boundary relations, so matrix-coordinate support data
  derived solely from that packet cannot prove the theorem. The packet-forced
  `19243` centrality consequence is the first concrete interior discriminator,
  but `Collision19243.lean` also proves that the parent-block word alone is an
  identity for every characteristic-two involution; the successful use must
  see the proper child/multiplicity refinement rather than the parent block.
- **Search by finite-coordinate min-cut after selection.** A viable loop is:
  compile relator consequences -> construct coordinate-dependent low-leakage
  subspaces or singular-value cuts in the finite multiplicity blocks -> build
  their weighted support graph -> run the exact min-cut backend -> replay the
  selected cut against all known exact finite countermodels.  The selection
  step is now the mathematical gate.
- **Respect the equalizer-density no-go.** Do not require one character sector
  to survive all compressor depths. The Hall set may aggregate many Fourier
  corners; only its total regular weight must stay positive.
- **The concrete Hall gap is discrete; only support deletion is missing.**
  `atlas-a8-mixed-block-transport-has-permutation-models` lists the fourteen
  A8 degrees and proves that every strict cut deficit on the 448 minimal
  Fourier vertices is at least `1/20160`.  It also realizes every rational
  regular-marginal transport plan by an exact permutation unitary after
  amplification.  Therefore `(AWH1)` needs no separate quantitative search
  for `gamma`: any strict deficient cut has a fixed gap.  Conversely, neither
  block-mass integrality nor the concrete multiplicities can create that
  cut.  The sole gate is relation-sensitive deletion/shrinkage of simultaneous
  within-block directions in `(AWH2)`.
- **One local block deletion is far below the Hall threshold.**
  `atlas-a8-hall-deficit-needs-439-forbidden-blocks` solves the concrete
  weighted support problem sharply: every deficient graph on the 448
  minimal Fourier vertices omits at least 439 source--target pairs.  The
  bound is attained by isolating one degree-70 minimal corner from all but a
  weight-64 nine-vertex neighborhood.  Therefore a projected relator minor
  is useful for hard Hall only if its common kernel implication propagates
  across a large orbit of block pairs.  A one-pair vanishing, or even 438
  unrelated pair vanishings, cannot close `(AWH1)`.
  In fact the same theorem constructs an exact `20160`-dimensional
  permutation absorber for every prescribed family of at most 438 forbidden
  pairs.  Thus a bounded minor calculation must be replayed through its full
  packet orbit and shown to suppress at least 439 distinct pairs before it
  has any hard-support force.
