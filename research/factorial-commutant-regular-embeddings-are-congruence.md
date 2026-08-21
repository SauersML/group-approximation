---
rg: 2
id: factorial-commutant-regular-embeddings-are-congruence
kind: claim
title: Every regular-trace embedding of the lattice algebra with factorial relative commutant is conjugate to a congruence-microstate embedding
distinct_from:
  sl3z-regular-microstates-are-congruence-correctable: that demands correction of EVERY regular-trace almost-representation; this demands it only for the extreme points of Brown's convex structure -- embeddings of L(SL_3(Z)) whose relative commutant is a factor -- and the route node reassembles the general case from these by disintegration, so this is the strictly smaller irreducible core.
  hnn-carrier-factorial-character-collapse: that is the factorial-CHARACTER form of the enemy on the HNN carrier (one group larger, no ambient algebra); this is the factorial-COMMUTANT form of the correctability input on the lattice algebra itself -- the same extremal compression applied on the microstate side instead of the trace side.
---

Claim: let `M = prod_U M_(d_m)` be a matrix ultraproduct and
`iota : L(SL_3(Z)) -> M` a trace-preserving embedding (so the group
trace is the regular character `delta_e`) whose relative commutant
`iota(L(SL_3(Z)))' cap M` is a FACTOR.  Then `iota` is unitarily
conjugate to an embedding whose microstates are genuine projective
congruence representations: there are representations `rho_m` of
`SL_3(Z)` factoring projectively through congruence quotients with
`u (iota(lambda))_m u* - rho_m(lambda) -> 0` in normalized HS for a
single unitary `u in M` and all `lambda`.

## Attempts

- **Why extremality is the right compression (2026-08-21,
  source-verified).**  Brown [Topological dynamical systems
  associated to II_1 factors, Adv. Math. 2011, arXiv:1010.1214]
  equips `Hom(N, R^U)` modulo unitary conjugacy with a complete
  metrizable convex-like structure (axiomatized by Capraro--Fritz,
  arXiv:1105.1270); its extreme points are exactly the embeddings
  with factorial relative commutant, and for property (T) algebras
  the extreme points are DISCRETE in the metric.  Atkinson's
  minimal-face/Schur analysis (arXiv:1608.08189) is the matching
  fine structure.  So the correctability demand on arbitrary
  microstates compresses to the extreme points, exactly parallel to
  the Krein--Milman compression that produced the factorial-character
  form of the collapse on the trace side.
- **The AKE calibration: exhaustion, not uniqueness.**
  Atkinson--Kunnawalkam Elayavalli [IMRN 2021] prove a separable
  tracial von Neumann algebra with CEP is amenable if and only if
  all embeddings into an ultraproduct II_1 factor are conjugate
  (equivalently, iff the embedding space is separable).  Since
  `L(SL_3(Z))` is non-amenable and embeddable, its embedding space
  is NON-separable: a Jung-type uniqueness statement is FALSE, and
  any correct correctability statement must be an EXHAUSTION
  statement -- the congruence-realized class is itself enormous
  modulo conjugacy (towers at different primes, different
  multiplicity profiles; property (T) rigidity separates them), so
  non-separability is consistent with exhaustion.  This claim is
  calibrated to pass exactly between those constraints.
- **Structural handles available at an extreme embedding.**  The
  relative commutant is a factor, the image algebra has property
  (T), and local rigidity holds: any embedding close to `iota` on a
  Kazhdan generating set is conjugate to it up to a small corner.
  So the claim is a LOCAL statement at each extreme point, and the
  congruence family supplies a known dense-in-itself set of extreme
  points (regular towers have factorial commutant along suitable
  subsequences).  What is missing is precisely a classification of
  extreme regular-trace embeddings -- the microstate mirror of
  classifying factorial hyperlinear characters of the carrier.
- **Falsification gate.**  A factorial-commutant regular-trace
  embedding NOT conjugate to any congruence-realized one would
  refute this claim and locate the hyperlinear enemy's microstates
  in an extreme, maximally structured object; the route node's
  disintegration argument would then convert any enemy of the
  correctability hole into such an object, so refutation here is
  refutation there -- the two claims stand or fall together, which
  is exactly what makes this the irreducible core.
- **Fiber dichotomy for the enemy (2026-08-21; wording corrected
  the same day -- the base of the disintegration is in general
  diffuse, see the route).**  Disintegrate the Lambda-restriction of
  an enemy's Gamma-embedding over the center `Z` of the relative
  commutant: `k in iota(Lambda)' cap M` commutes with `Z`, so `k`
  is decomposable, `k = integral k_z`, with `k_z` in the fiber
  commutant `Q_z` (a factor).  Two cases.
  (a) Every fiber has SCALAR commutant: then `k in Z` is a function
  on the base and the enemy is an abelian coupling -- a countable weighted
  atom system on which `Gamma` acts through the Hecke
  correspondence (Lambda_-/Lambda_+ refinements exchanged by `h`),
  whose commutator profile is a spherical coefficient of the
  far-defect formula; this is the coset-Bernoulli/quasi-regular
  family, with its extreme profile the separately attacked hole
  `no-exact-quasi-regular-leak`.  CHECK against the canonical
  enemy: in the coset-Bernoulli crossed product the Lambda-
  commutant is exactly `L^infinity(X)^Lambda` (abelian: the
  Lambda-conjugacy class of every `g notin Lambda` is infinite), so
  the canonical enemy is precisely case (a) with diffuse base.
  (b) Some fiber has NON-scalar factorial commutant hosting `k_z`: then by
  `hnn-carrier-enemy-moment-splitting` the Gamma-commutant tensor-
  splits off `L(Gamma)`, so `k_atom` lives in `Q_(Lambda,atom)`
  strictly above the tensor-split `Q_(Gamma,atom)` -- the enemy
  needs Lambda-fibers whose commutant is a genuine amplification
  factor NOT absorbed by the Gamma-structure.  This splits the wall
  into two named sub-walls (abelian coupling; non-scalar fibers),
  each with its own existing instruments, and the non-scalar case
  is the one the extreme-point classification must address.
