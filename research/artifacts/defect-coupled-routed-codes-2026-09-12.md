# Defect-coupled codes over the Leavitt units: one combining stage plus routing never compresses

Lane `w3-measurable`, 2026-09-12. Supports `single-maximal-stage-routed-codes-cannot-compress`,
`compression-codes-are-small-generating-partitions` and
`profinite-localization-is-vacuous-over-leavitt-units`, and records where the defect-coupling ansatz
for `measurable-alphabet-compression-over-leavitt-units` dies.

Notation as in `research/artifacts/measurable-alphabet-compression-2026-09-12.md` Section 0: left shift
`(h.x)(g) = x(h^-1 g)`, uniform product measure `mu_A`, codes are Borel, equivariant, and injective on
a conull set. `U = L_(F_2)(1,2)^x`.

## 1. The ansatz this artifact tests

The directive was to couple the rigid defect `d = [t z t^-1, gamma]` (invisible to every finite model)
with the nonamenable actor of `U`. Its most natural form has two ingredients:

* **Local combining along the defect.** A stage `S` merges input symbols at `p` and `pd`, possibly
  together with finitely many actor elements, into one output symbol: `S(x)(g) = f((g^-1.x)|_K)` with
  window subgroup `K`.
* **Transport along the actor.** Before and after `S`, symbols move along the nonamenable actor by
  Borel routing codes of the kind in Theorem A of the compression artifact: a certificate track `c` is
  kept, and each output data site is filled from one input data site, with arbitrary Borel routing and
  unbounded displacement.

The hope was that routing supplies the Hilbert-hotel space and the defect supplies the redundancy.
Section 2 shows this factorization never compresses whenever the combining stage sees only a sofic
(for instance amenable) subgroup, however wild the routing.

## 2. Theorem C: a single maximal combining stage between routings never compresses

**Setting.** `G` is a countable group, `A = C x D` a finite alphabet with `mu = mu_A`, and `K <= G`.

* `R_1: A^G -> A^G` is a routing code as in Theorem A: `R_1(c, d) = (c, y)` with
  `y(g) = pi_c(g)(d(rho_c(g)))`, `rho` and `pi` Borel and equivariant.
* `S: A^G -> E^G` is `S(x)(g) = f((g^-1.x)|_K)` for a Borel `f: A^K -> E`.
* `R_2: E^G -> B^G` is any Borel equivariant map with `|B| = |E|`, for instance a routing code on
  `E = C' x D'`.

**Theorem C.** Suppose `tau = R_2 o S o R_1` is injective on a `mu`-conull set, and the uniform
Bernoulli shift over `K` at alphabet `A` has maximal Rokhlin entropy, `h^Rok_K(A^K, mu_A) = log |A|`
(or `K` is finite). Then `|B| >= |A|`. In particular, if `K` is sofic, no such `tau` is a compression.

*Proof.*

1. **The first routing is a measure-preserving bijection.** `tau` is injective on a conull set, so
   `R_1` is. By Theorem A (`measurable-certificate-routing-preserves-bernoulli-measure`),
   `(R_1)_* mu = mu`. Let `X_0` be a conull Borel set on which `tau` is injective. `R_1` is injective on
   `X_0`, so by Lusin–Souslin `Y_0 = R_1(X_0)` is Borel. Since `(R_1)_* mu = mu` and
   `R_1^-1(Y_0) ⊇ X_0`, `mu(Y_0) = mu(R_1^-1(Y_0)) = 1`.
2. **The combining stage is injective on a conull set.** For `y, y'` in `Y_0` with `S(y) = S(y')`, write
   `y = R_1(x)` and `y' = R_1(x')` with `x, x'` in `X_0`. Then `tau(x) = tau(x')`, so `x = x'` and `y = y'`.
   So `S` is injective on the conull set `Y_0` for the uniform measure `mu`.
3. **Descent.** By `bernoulli-codes-descend-to-window-subgroup`, `S_K(z)(k) = f(k^-1.z)` on `A^K` is
   injective on a conull set.
4. **Maximality.**
   * If `K` is finite, `mu_A` on `A^K` gives every point positive mass, so `S_K` is injective. An
     injective map `A^K -> E^K` forces `|E| >= |A|`.
   * If `K` is infinite, Proposition 1 of the compression artifact over `K` gives
     `h^Rok_K(A^K, mu_A) <= log |E|`. Maximality gives `log |A| <= log |E|`.
5. **Conclusion.** `|B| = |E| >= |A|`. Sofic groups are Rokhlin-maximal at every alphabet by the
   Sofic-groups consequence of `sofic-radical-localizes-bernoulli-deficit-witnesses`. QED

**Remarks.**

* **What routing buys.** Nothing, for compression. Routing may carry symbols along the nonamenable actor
  with unbounded Borel displacement, yet it is a measure-preserving bijection almost everywhere
  (Theorem A), so it cannot create room for a combining stage that the stage's own window subgroup does
  not already provide.
* **Relation to descent.** `bernoulli-codes-descend-to-window-subgroup` already rules out a compression
  whose whole window generates a sofic subgroup. Theorem C is stronger in one direction: the composite
  `tau` reads, through `R_1` and `R_2`, coordinates in every direction of `G` with unbounded
  displacement, so its effective window generates all of `G`. Only the combining stage is constrained.
* **Scope of `R_2`.** Only alphabet preservation is used, not Theorem A.
* **Consequence for the defect ansatz over `U`.** Any combining stage whose window generates an
  amenable, residually finite or otherwise sofic subgroup is dead, whatever routing surrounds it. That
  includes windows inside `<d>` together with finitely many elements generating a sofic subgroup. So
  the coupling cannot be split into "code locally along the defect, then transport along the actor".
  The combining itself must read a window generating a nonsofic subgroup. By the localization theorem
  that subgroup contains an invisible difference, and by the census in
  `research/artifacts/two-root-identity-nonsofic-mechanism-2026-09-12.md` every subgroup containing
  the nine-leaf configuration is a copy of `U` itself.

## 3. Proposition D: compression codes are small generating partitions

**Proposition D.** Let `G` be countably infinite and `A, B` finite. There is a Borel equivariant code
`tau: A^G -> B^G` injective on a conull set iff the uniform Bernoulli shift `(A^G, mu_A)` has a Borel
partition with `|B|` pieces whose translates generate the Borel sigma-algebra modulo null sets.

*Proof.*

* **Code to partition.** Proposition 1 of the compression artifact: `beta_b = {x : tau(x)(1) = b}`.
* **Partition to code.** Let `beta = {beta_b : b in B}` be generating modulo null sets, and put
  `tau(x)(g) = b` exactly when `g^-1.x` lies in `beta_b`. Then
  `tau(h.x)(g) = b` iff `g^-1 h.x` lies in `beta_b` iff `tau(x)(h^-1 g) = b`, so `tau(h.x) = h.tau(x)`.
  Take a countable separating family `{B_n}` of Borel sets. Each `B_n` agrees, off a null set `N_n`,
  with a set `A_n` in the sigma-algebra generated by the translates of `beta`. On the conull set
  `X_0 = complement of the union of the N_n`, the sets `A_n ∩ X_0 = B_n ∩ X_0` separate points, and any
  two points with the same `tau`-value are not separated by any `A_n`. So `tau` is injective on `X_0`.
  QED

So designing a compression is exactly designing a generating partition with fewer pieces than the
base alphabet. The defect-coupling ansatz is a proposal for such a partition, whose pieces are read
through the combining window. Theorem C says those pieces can never be read through a single sofic
window, even with Borel routing before and after.

## 4. Proposition E: closedness in the ambient profinite topology of U filters nothing

**Proposition E.** Every proper subgroup of `U` fails to be closed in the profinite topology of `U`.

*Proof.* `U` is infinite and simple (`binary-leavitt-unit-group-is-simple`). A finite-index subgroup
contains its normal core, which is a finite-index normal subgroup, hence `U` itself. So `U` has no proper
finite-index subgroup, the profinite topology of `U` is indiscrete, and the closure of every subgroup is
`U`. QED

**Scope (corrected after review by `w3-vf-nonlinear`).** Proposition E concerns only the ambient
profinite topology of `U`. The localization theorems constrain the subgroup `K` generated by a witness:
- `kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers` measures closedness in the profinite
  topology of `pi(K)`. Over `U` the relevant `K` can be residually finite, and there closedness is a
  genuine condition.
- `sofic-radical-localizes-bernoulli-deficit-witnesses` constrains `Rad(K)`, which is nontrivial only
  for nonsofic `K`. So invisibility is not automatic at the level of a witness, even though
  `Rad(U) = U`.

An earlier version of this section said the non-closed-stabilizer localization has no analogue over `U`
and that invisibility is automatic there. Both overstated Proposition E: what it removes is only the
ambient version of the filter. The witness-level filters still bite over `U`, alongside the nonsoficity
of the combining window (Section 2) and the measure obstructions of the compression artifact.

## 5. Where it stops

* **Two or more combining stages.** Theorem C covers one combining stage between routings. A composite
  of combining stages along different sofic subgroups is not covered. Their windows together can
  generate a nonsofic group, and the intermediate measures are not Bernoulli, so descent does not apply
  stage by stage. The Ornstein–Weiss radius-one code over `F_2`, combining along `a` and `b`, shows that
  per-stage accounting fails once two directions combine. Any synergy must live there, and over `U` the
  combined window must generate a copy of `U`.
* **What a construction must be.** A generating partition of `(A^U, mu_A)` with fewer than `|A|` pieces
  whose pieces cannot be computed, even after Borel routing, by any single stage reading a sofic
  window. No such partition is known, and every known lower-bound device goes through finite models.
* **What an obstruction must be.** An invariant of generating partitions over `U` that sees the
  nonsofic combining window. Conjugacy invariants are inert
  (`measure-conjugacy-invariants-cannot-certify-surjectivity`), so it must use the coordinate partition.
