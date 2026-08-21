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

**Step 2 (disintegration over the relative commutant --
CORRECTED 2026-08-21).**  Let `Z = Z(iota(N)' cap M)` be the center
of the relative commutant.  Disintegrating `iota` over the spectrum
of `Z` gives fibers whose relative commutants are factors -- extreme
points of Brown's convex-like structure [arXiv:1010.1214; axiomatics
arXiv:1105.1270].  The base is in general DIFFUSE: for the canonical
coset-Bernoulli enemy the Lambda-commutant is `L^infinity(X)^Lambda`,
which contains the shell averages of the lamp coordinates, a
diffuse algebra (an earlier draft claimed an atomic decomposition;
that is false).  What property (T) gives is weaker and sufficient:
extreme points are discrete in Brown's metric and two fibers that
are close on a Kazhdan generating set are conjugate, so the
measurable class map from the base to the (discrete) set of
conjugacy classes of extreme embeddings has COUNTABLY many classes
of positive measure, and
`iota|_Lambda = direct_sum_i  pi_i  tensor  1_(L^infinity(Z_i))`:
countably many extreme embeddings, each amplified by a diffuse (or
atomic) abelian multiplicity algebra.  This needs (T); for free
groups the class set is not discrete and the argument fails.

**Step 3 (correct each class, then reassemble).**  The required
claim corrects each factorial-commutant class representative
`pi_i` to a congruence-realized embedding; abelian amplification
preserves the congruence class (tensor the microstates with
diagonal matrices, i.e. take direct sums of copies).  The congruence-realized class is closed under
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
