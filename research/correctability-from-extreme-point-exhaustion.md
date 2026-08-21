---
rg: 2
id: correctability-from-extreme-point-exhaustion
kind: route
title: DV stability plus Brown disintegration reassembles correctability from its factorial-commutant extreme points
target: sl3z-regular-microstates-are-congruence-correctable
requires:
  - factorial-commutant-regular-embeddings-are-congruence
---

**Step 1 (from almost-representations to embeddings).**  A regular-
trace almost-multiplicative sequence `sigma_m` defines a
trace-preserving embedding `iota : L(SL_3(Z)) -> M = prod_U M_(d_m)`
(the trace is `delta_e`, whose GNS closure is the group factor).
Conversely any HS-correction of the embedding's microstates corrects
`sigma_m` on the generating set, so the microstate claim is
equivalent to: every regular-trace embedding of `L(SL_3(Z))` into a
matrix ultraproduct is unitarily conjugate to a congruence-realized
one.  (Dogon--Vigdorovich hyperfinite HS-stability, unconditional at
`SL_3(Z)` by character rigidity, already normalizes the almost-
representation into a genuine embedding picture with controlled
trace; the content left is where the embedding sits.)

**Step 2 (disintegration over the relative commutant).**  Let
`Z = Z(iota(N)' cap M)` be the center of the relative commutant.
Cutting `iota` by the spectral projections of `Z` decomposes the
embedding into pieces whose relative commutants are factors --
extreme points of Brown's convex-like structure on the embedding
space [arXiv:1010.1214; axiomatics arXiv:1105.1270].  Property (T)
of `SL_3(Z)` makes the extreme points discrete and gives local
rigidity: two extreme pieces that are close on a Kazhdan generating
set are conjugate up to small corners.  The step to write carefully
(flagged, not assumed): measurable selection plus discreteness
upgrades the disintegration to a COUNTABLE weighted direct sum of
factorial-commutant embeddings -- the atomicity uses (T), not
generalities, and fails for free groups.

**Step 3 (correct each atom, then reassemble).**  The required
claim corrects each factorial-commutant atom to a congruence-
realized embedding.  The congruence-realized class is closed under
countable direct sums with matrix-ultraproduct weights (interleave
levels; project weights onto dyadic corners with vanishing error)
and is closed in the embedding metric (diagonalize corrections),
so the corrected atoms reassemble into a congruence-realized
embedding conjugate to `iota`.  With Step 1 this yields the full
microstate statement, hence `(RC3)` through the Weyl sector theorem
and the goal through the p = 3 wiring.

**Interface notes.**  (i) The reassembly tolerates the projective
and flexible allowances of the target claim verbatim -- atoms may be
corrected projectively and with vanishing corner defects.  (ii) The
enemy direction sharpens symmetrically: an enemy of the target
yields, through Steps 1-2, a factorial-commutant regular embedding
not conjugate to any congruence one -- the microstate mirror of the
factorial hyperlinear enemy character, and the two compressions
(Krein--Milman on traces, Brown extreme points on embeddings) are
now recorded as one mechanism seen from both sides.
