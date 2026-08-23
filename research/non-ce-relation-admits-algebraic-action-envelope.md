---
rg: 2
id: non-ce-relation-admits-algebraic-action-envelope
kind: claim
title: The non-CE relation algebra embeds into one algebraic compact abelian crossed product
distinct_from:
  non-ce-property-t-equivalence-relation-exists: that establishes existence of the non-CE relation factor by IRS and property-T envelope; this demands a second, ALGEBRAIC envelope — compact abelian base, automorphic action, Haar measure — so that Pontryagin duality applies.
  algebraic-envelope-principle: that is the established compiler consuming this hole; this is the construction obligation itself.
  kun-thom-clifford-crossed-product-ce: that asks whether one specific Clifford crossed product is CE; this asks to place a KNOWN non-CE algebra inside some algebraic crossed product, with full freedom in choosing the base and the acting group.
---

Construct a compact second-countable abelian group `K`, a countable
group `Lambda` acting on `K` by continuous automorphisms, and a
trace-preserving embedding

```text
L(R)  ->  L^infinity(K, Haar) rtimes Lambda,               (AAE1)
```

where `L(R)` is the non-Connes-embeddable relation factor of
`non-ce-property-t-equivalence-relation-exists`.  Any non-CE tracial
algebra in place of `L(R)` is equally acceptable.  By
`algebraic-envelope-principle` this alone produces the explicit
non-hyperlinear group `hat K rtimes Lambda`.

## Attempts

- **Correlated one-hot Haar registers do not give a cheaper compiler
  (2026-08-22).**  `correlated-haar-onehot-dichotomy` computes the exact
  finite-marginal density for every linear code/subshift.  High rank forces
  exponential density loss; good distance does not help, as diagonal
  repetition has distance one and constant density.  If the surviving
  conditional law is affine Haar, every one-coordinate one-hot alphabet has
  size at most two (one for odd characteristic), so genuine multiway control
  is lost.  If instead a positive invariant nonlinear one-hot corner retains
  the BCS holonomy, that corner is already a non-CE subalgebra of the
  algebraic crossed product and solves `(AAE1)` directly.  Finite selector
  image reduces further to matrix algebras over stabilizer fiber actions.
  Thus the exact survivor is an infinite-image nonlinear positive corner,
  but constructing its holonomy is the envelope problem itself; ordinary
  LDPC correlations do not bypass it.

- **Haar linear subshift design.**  The natural candidates are closed
  shift-invariant subgroups `K <= (F_p^m)^Lambda` cut out by finitely
  many linear local rules: the action is algebraic by construction,
  Haar is the natural measure, and the dual `hat K` is a finitely
  generated `F_p[Lambda]`-module, so `hat K rtimes Lambda` is finitely
  generated and recursively presented.  The decisive design constraint
  is to make the non-CE witness's invariant measure HAAR, not merely
  shift-invariant: for non-Haar measures the duality `(AEP1)` fails and
  the compiler does not apply.  This is a new reading of the existing
  finite-field/LCS gadget library: as measure-algebraic processes, not
  as robust matrix decoders — no finite-dimensional soundness theorem
  is needed at the compiler stage.
- **Freeness is a convenience, not an obstacle.**  If a candidate
  action is not essentially free, tensor with an algebraic Bernoulli
  shift `(F_p)^Lambda`: products of algebraic actions are algebraic,
  freeness is restored, and an embedding `(AAE1)` into the smaller
  crossed product persists into the larger one.  The subtle point is
  to secure the inclusion at the crossed-product level first; a non-CE
  QUOTIENT of a crossed product proves nothing here.
- **Where the obvious attempt dies.**  The property-T relation
  envelope behind the established input is a wreath-like construction
  on a p.m.p. base that is not visibly algebraic; simply declaring the
  base to be a group rotation fails because the envelope's measure is
  built from the IRS, and nothing forces it to be Haar on any group
  structure.  The genuine work is either (a) re-run the envelope
  construction inside the category of algebraic actions — the
  wreath-like extension of an algebraic action by a finite-field
  module IS algebraic, so the question is whether the IRS trace can be
  realized on an algebraic base — or (b) design a new non-CE witness
  natively as a Haar linear subshift, using the correlation-to-module
  dictionary.
- **The unrestricted wording is circular.**
  `unrestricted-algebraic-envelope-equals-nonhyperlinearity` proves
  that existence of *some* non-CE algebra inside *some* compact-abelian
  algebraic crossed product is equivalent to existence of a non-hyperlinear
  group: Fourier duality gives the forward implication, while the one-point
  compact group gives the converse.  Therefore the phrase "any non-CE
  tracial algebra is equally acceptable" cannot itself define a cheaper
  route.  The only noncircular content here is the fixed-source requirement
  (embed the already constructed `L(R)`) together with independently useful
  restrictions on the actor or module.
- **The cited universal property-(T) envelope does not fill the gap.**
  `cdi-property-t-envelope-has-nonabelian-base` audits the primary
  Chifan--Drimbe--Ioana construction.  Its target has the explicit form
  `M_tilde^C rtimes_(beta,w) C`, with nonabelian tensor base `M_tilde^C` and a
  cocycle action.  Their Remark 1.1 says that embedding universality of group
  factors remains open.  Thus neither "generated by a property-(T) group
  representation" nor the relation analogue produces the Haar abelian base
  required by Pontryagin duality.  In fact their theorem gives a non-CE
  character on a residually finite property-`(T)` hyperbolic group; its
  canonical group trace remains CE.  This is a concrete demonstration that
  the missing datum is trace promotion, not group generation.
- **Source-structure triage (2026-08-21, from arXiv:2502.06697v2).**
  The witness's acting group is `*_Q Z_2^m x Z_2` — a free product of
  finite abelian `2`-groups, hence VIRTUALLY FREE: excellent for
  subshift design (tree-shifts over virtually free groups have strong
  effective theory), and `hat K rtimes Lambda` would be (finitely
  generated module)-by-(virtually free), certainly recursively
  presented.  The IRS trace is `tau_H` on the free group with
  `L(Gamma/H) = tau_H(Gamma)''` non-CE because a tailored game has
  `omega_IRS > omega*` (TailoredMIP* = RE); the base pmp space is the
  abstract GNS/stabilizer space, NOT a group.  The naive
  algebraization fails at a precise point: `Sub(Gamma)` inside
  `{0,1}^Gamma` is a closed shift-invariant SUBSET but not a
  subGROUP — subgroup indicators are not closed under addition — so
  the stabilizer realization is a subshift, never a linear subshift,
  and no Haar structure comes for free.
- **Sharpened branch (a): algebraic completeness for one tailored
  game.**  In `L^infinity(K) rtimes Lambda` for a Haar linear subshift
  `K <= (F_2^m)^Lambda`, order-two dual characters give native
  `±1`-observables, and correlations of character/group words are
  normalized solution counts of linear systems over the
  `F_2[Lambda]`-module `hat K`: Haar-module strategies realize exactly
  LCS-type correlations.  Branch (a) therefore reduces to: can the
  COMPLETENESS (honest) strategies of one tailored halting game with
  `omega_IRS > omega*` be taken in module/Haar form — i.e., is
  `omega_alg > omega*` for some such game?  A positive answer places
  the non-amenable trace on `L(hat K rtimes Lambda)` and closes this
  hole outright; a negative structural answer (module strategies
  provably amenable-dominated) kills branch (a) and concentrates all
  effort on branch (b).  This meshes with the graph's existing
  LCS/BCS compiler lane, but consumes only completeness-side
  structure — no robust finite-dimensional soundness is needed.
- **Necessary condition (proved, 2026-08-21): the dual module must not
  be residually finite.**  If `hat K` admits a separating family of
  finite `Lambda`-invariant-cofinite submodules and `Lambda` is
  residually finite (virtually free groups are), then
  `hat K rtimes Lambda` is residually finite, hence sofic, hence
  hyperlinear, and `L^infinity(K) rtimes Lambda` is Connes embeddable
  — no non-CE algebra can embed, and the envelope fails for that `K`.
  (The free module `F_2[Lambda]^m` itself IS residually finite —
  separate a finite support by a finite quotient of `Lambda` — so
  full shifts and any subshift with residually finite dual are
  barren.)  The defining linear rules must therefore produce a
  NON-residually-finite `F_2[Lambda]`-module: the algebraic shadow of
  the non-soficity we are trying to manufacture.  Note the general
  abelian-kernel extension problem (`A` abelian, `G/A` sofic, is
  `A rtimes Lambda` sofic?) is OPEN — this lemma uses only the
  residually finite case, so the envelope is not killed, but it is
  squeezed exactly onto modules with no separating finite invariant
  structure.  This doubles as a screen for the algebraic-completeness
  branch: if tailored-game module strategies can always be taken over
  residually finite modules, that branch dies.
- **The design box (2026-08-21, second pass): index dictionary and
  virtual triviality.**  For an algebraic action the fixed set of every
  element is a CLOSED SUBGROUP, so the crossed-product trace obeys the
  dictionary `tau(u_w) = Haar(Fix w) = 1/[K : Fix(w)]`, with value `0`
  at infinite index: algebraic IRS characters are exactly the
  index-reciprocal profiles of stabilizer subgroup lattices.  A
  non-CE GNS forces some `w != e` with `tau(u_w) > 0` (otherwise the
  character is regular and the GNS is `L(Lambda_0)`, CE since
  `Lambda_0` is virtually free).  For such `w`, `[K : Fix(w)]` finite
  dualizes to `(w-1) hat K` FINITE; and by
  `(st-1) = s(t-1) + (s-1)`, finiteness of `(s-1) hat K` on a
  generating set propagates to every word of the generated subgroup.
  So the enemy module must be VIRTUALLY TRIVIAL element-by-element on
  the whole positive-trace subgroup while remaining globally
  non-residually-finite (previous bullet) — a very tight box: each
  listed element moves only a finite chunk of the dual, yet no
  separating finite invariant structure exists globally.
- **Deciding `omega_alg > omega*` IS the goal, not a preliminary.**
  A positive answer makes `hat K rtimes Lambda_0` non-hyperlinear
  outright, so no cheap decision should be expected; the actionable
  work is the box above plus the finite-type screen: **does a
  finitely presented non-residually-finite `F_2[F_k]`-module exist?**
  If no, finite-type linear tree-shifts can never carry the envelope
  and recursively-enumerable rules are forced (the Higman step then
  does real work); if yes, the witness modules are the candidate
  bases.  This is a clean, well-posed question in the algebra of
  free group rings — the module-language form of the periodic-density
  screen — and it is where this hole should be attacked next.
- **The finite-type screen is now closed (proved, 2026-08-21).**
  Garrido--Jaikin-Zapirain, Proposition 5.3, prove that every finitely
  presented module over `F_p[F]`, for `F` a finitely generated free group, is
  residually finite.  Restriction to a finite-index normal free subgroup and
  intersection of finitely many conjugate separating submodules extends this
  to every finitely generated virtually free group.  The dual of a finite-type
  linear subshift is finitely presented, so
  `finite-type-linear-vfree-envelope-is-residually-finite`
  proves that EVERY finite-type Haar-linear subshift over the Manzoor source
  group has residually finite semidirect product and a Connes-embeddable
  crossed product.  Thus the question in the preceding bullet has answer NO:
  a finitely presented non-residually-finite `F_2[F_k]`-module does not exist.
  Branch (a) can survive only with infinitely many r.e. module relations, a
  different acting group, or a genuinely non-Cartan embedding.  Enlarging a
  finite local rule table can never help.
- **The native virtually-free actor is completely closed (proved,
  2026-08-21).**  `abelian-by-virtually-free-groups-are-sofic` removes the
  finite-type hypothesis entirely.  For every countable abelian module `A`,
  `A rtimes F_r` is an iterated HNN extension over the amenable subgroup `A`,
  hence sofic; a normal finite-index free subgroup and sofic-by-amenable
  permanence extend this to every finitely generated virtually free actor.
  Therefore every compact-abelian Haar crossed product with the native
  Manzoor actor is CE, even for infinitely related/non-residually-finite
  modules, and even if the desired inclusion is non-Cartan.  Any surviving
  algebraic envelope must change the acting group.
- **Branch (b) collapses onto the Kun--Thom coset module (2026-08-21,
  third pass).**  Following the design box constructively: non-r.f.
  duals with positive-trace elements exist cheaply in the ABELIAN
  world (`Z[1/6] rtimes_(3/2) Z = BS(2,3)` is non-r.f. with algebraic
  dual action), but every such solvable example is amenable, hence
  sofic, hence CE — barren.  To escape soficity the module must sit
  over a coset space with NON-amenable stabilizers, and the minimal
  such design is `plus_(Gamma/Lambda) F_2` with the coset action —
  literally the coset Bernoulli / Kun--Thom wreath module already held
  by the graph (`coset-bernoulli-ce-refutes-relative-commutant-collapse`,
  `kun-thom-clifford-crossed-product-ce`, and the wreath route
  `nonhyperlinear-coset-wreath-from-commutant-collapse`).  So branch
  (b)'s design pressure reproduces the existing fork rather than
  opening new space: the envelope lane's genuinely new content beyond
  the recorded coset/KT questions is exactly branch (a) — the
  `omega_alg` completeness question — plus the freedom to choose
  OTHER non-amenable-stabilizer coset modules than the arithmetic
  ones (e.g. over the graph's own nonsofic group), which is the one
  degree of freedom the KT fork does not already exhaust.
- **Z-alignment is the algebraic format (2026-08-21, from the
  Aldous--Lyons papers arXiv:2408.00110 and arXiv:2501.00173).**  In
  the subgroup-test framework the completeness side of the halting
  reduction is a perfect Z-ALIGNED permutation strategy (readable
  variables diagonal) commuting along edges.  Z-alignment is exactly
  diagonality in a distinguished basis — and Haar-module strategies
  are Z-aligned in the FOURIER basis: order-two dual characters are
  the diagonal readables of the algebraic world.  Branch (a) is
  therefore formally: does the value of the separating subgroup tests
  over Z-ALIGNED HAAR-ALGEBRAIC strategies (stabilizer IRSs of
  algebraic actions, per the index dictionary above) still exceed the
  quantum/co-sofic bound?  The design box says exactly which
  algebraic IRSs are available: index-reciprocal profiles with
  element-wise virtual triviality on the positive-trace subgroup and
  no separating finite invariant structure.  This is the right
  meeting point of this hole with the subgroup-test technology, and
  it makes branch (a) a question ABOUT the BCLV completeness
  construction rather than about an abstract envelope.
- **Falsification test.**  Fourier positivity is a real constraint:
  coefficients of Haar algebraic processes satisfy character-positivity
  identities that a general p.m.p. correlation need not.  Check the
  imported witness's correlations against these identities first; a
  clean violation on every algebraic re-realization would kill route
  (a) and redirect all effort to (b).
- **Stacking finite Fourier-binary compilers is still barren (proved,
  2026-08-21).**  One might try to evade the finite-partition obstruction by
  adjoining countably many finite `SL_3(Z)`-invariant Haar-linear factors,
  hoping that their union generates the source action and that the total
  actor image becomes infinite.  This does not work.
  `stacked-finite-haar-modules-are-residually-finite` proves that for every
  residually finite actor `H` and every coordinatewise action on
  `K=product_n K_n` with each `K_n` finite abelian, the dual semidirect
  product `(direct_sum_n K_n-hat) rtimes H` is residually finite.  The proof
  separates an actor element in a finite quotient of `H`, and separates a
  dual lamp element on its finite invariant coordinate support.  Thus even a
  GENERATING infinite family satisfying the Fourier-binary test is CE when
  it is assembled as an independent product of finite invariant layers.
  Any surviving native Haar-linear `SL_3(Z)` construction must introduce
  nonsplit relations coupling arbitrarily late layers; its dual module cannot
  be a direct sum of finite invariant submodules.
- **Nonsplit finite layers are still barren (proved, 2026-08-23).**  The
  preceding direct-product fence extends to arbitrary inverse systems.
  `inverse-finite-algebraic-actions-are-ce` dualizes an inverse limit of
  finite invariant `H`-groups to a filtered colimit of finite `H`-modules.
  The dual semidirect product is then the directed union of the finite-by-`H`
  stages, hence sofic whenever `H` is sofic.  Neither injectivity nor an
  equivariant splitting of the bonding maps is used.  Consequently coupling
  arbitrarily late finite `SL_3(Z)` layers by nonsplit bonding relations does
  **not** suffice: every such inverse-finite construction is CE.  A survivor
  must contain a finitely generated dual submodule that is not contained in
  the image of any finite invariant module, rather than merely fail to be a
  direct sum of its finite layers.
- **The published Manzoor witness has no exposed cylinder law
  (source audit, 2026-08-21).**
  `manzoor-separation-does-not-specify-haar-cylinders` expands the exact game
  correlation: it is a finite linear combination of one-word probabilities
  `Pr[w in H]`, not the joint cylinders `Pr[F subset H]` tested by Haar
  fixed-subgroup indices.  The only explicit values forced by the strategy
  axioms are `0` for `J` and `1` for squares and prescribed commutators, all
  compatible with the reciprocal-index screen.  More fundamentally,
  Theorem 3.13 obtains an unnamed separating game by contradiction, then
  chooses an unspecified above-gap IRS strategy, and the final ergodic step
  chooses an unspecified extreme IRS.  There is therefore no canonical
  "Manzoor IRS" cylinder oracle to test.  Literal equality with Haar measure
  on a linear subshift of subgroup indicators is impossible because the
  identity-membership coordinate is constantly one, but this formal obstacle
  is no longer load-bearing: `affine-haar-process-fourier-modulus-compiler`
  permits affine Haar laws and homogenizes that constant phase with one extra
  scalar coordinate.  The substantive stabilizer-pushforward/factor question
  remains open.  Running the proposed falsification test now first requires
  `explicit-zpc-irs-gap-game-witness` or another named strategy with joint
  cylinder data; the published existential separation alone cannot supply a
  violating cylinder.  The sharpened test is whether every such Fourier
  moment has modulus zero or one.
- **ZPC does not force the sharpened test, and passing it is not trace
  promotion (2026-08-21).**
  `zpc-does-not-force-affine-haar-membership-law` gives a perfect six-point
  ZPC permutation strategy whose single membership-bit Fourier moment is
  `1/3`; hence neither Z alignment, edge commutation, nor perfect acceptance
  implies affine Haar.  More fundamentally,
  `affine-haar-membership-does-not-promote-irs-trace` takes a Dirac normal
  subgroup IRS: its membership law is an affine-Haar singleton, but the name
  action crossed product is `L(Gamma)` while the IRS GNS algebra is
  `L(Gamma/N)`, and the canonical actor traces disagree on every
  `n in N\{e}`.  Thus even a successful cylinder audit would not by itself
  retain the non-CE algebra.  The exact surviving target is a nonlinear
  equivariant factor whose crossed-product pullback retains the non-CE
  relation/GNS algebra and its normalizers, as in `(HSD1)`, or a genuinely
  non-Cartan embedding.  Joint membership moments alone are insufficient.
- **Random coset lamps recover the IRS values exactly but do not promote the
  trace.**  `random-coset-lamp-correlations-realize-every-irs-character`
  forms `W_H=(directSum_(Gamma/H) C_2) semidirect Gamma` and observes
  `tau(a_H g a_H g^(-1))=1_(g in H)`.  Direct integration over the IRS gives
  `phi_mu(g)` exactly in a measurable field of wreath factors.  The returned
  words are not multiplicative in `g`, while the honest actor unitaries retain
  the regular trace, so no IRS GNS embedding follows.  Moreover
  `finite-profinite-lamp-packets-cannot-carry-manzoor-trace` proves every
  finite, countably mixed finite, or profinite version has a CE permutation
  character.  Thus the lamp formula is the correct local moment identity,
  but converting its random bundle into one group factor is exactly `(AAE1)`
  or an equally strong non-Cartan group-factor envelope; packet limits cannot
  perform that conversion.
- **The Mihailova quotient has no canonical kernel-killing corner (proved,
  2026-08-23).**  In the coset-lamp group factor, the free-cover kernels act
  trivially on the lamp base but their canonical group unitaries remain in
  the regular representation.  `infinite-kernel-canonical-compression-is-zero`
  proves that no nonzero projection anywhere in the full crossed product can
  satisfy `p u_n p=p` for every element of either infinite kernel: such a
  projection would be a nonzero invariant vector for the restriction of the
  regular representation to an infinite subgroup.  Hence one cannot recover
  `Q` or its left-right algebra by compressing the canonical actor copy and
  killing the kernel, even with a genuinely non-Cartan projection.  The live
  Mihailova mechanism must instead Fourier-mix the actor grades or solve the
  state-specific projective cross-stability problem already isolated in
  `mihailova-actor-liftable-ce-forces-q-hyperlinear`.
- **Orthogonal bounded Fourier support reduces to a finite-range cocycle,
  and does not collapse (proved, 2026-08-23).**
  `orthogonal-finite-fourier-reps-are-orbit-cocycles` classifies every
  candidate of the form `V_a=sum_g u_g p_(a,g)` with orthogonal source and
  range projections.  Unitarity is exactly the pair of partition identities,
  multiplication is the explicit finite cocycle equation `(OFC3)`, and the
  canonical trace is the mass of the identity-labeled piece.  A three-grade
  transposition supported on `{e,g,g^(-1)}` is already a nonhomogeneous exact
  involution when `g` has infinite order.  Thus the hoped-for bounded-support
  orthogonality collapse is false.  The live normalizer subproblem is now
  sharp: construct or exclude a regular-trace finite-range cocycle for the
  source multiplication table inside the Mihailova left-right Bernoulli
  relation.  Nonnormalizing Fourier coefficients lie instead in the existing
  Hadamard-cell assembly, which is equivalent to the full ambient-envelope
  problem.
- **The full orthogonal finite-range Mihailova branch is impossible (proved,
  2026-08-23).**  Choose the finitely presented nonsofic quotient `Q` to be
  the infinite property-`(T)` Fournier--Facio group.  Since
  `F_m times F_m` is Haagerup,
  `kazhdan-finite-cocycles-cannot-enter-haagerup-actions` excludes every
  regular-trace solution of `(OFC1)`--`(OFC3)`, with arbitrary mixed finite
  actor supports.  The proof freely Bernoulli-stabilizes the host, turning
  the cocycle into a free `Q`-subrelation of a Haagerup relation.  Haagerup
  passes to subrelations, whereas the resulting `Q`-relation has property
  `(T)`; a relation with both properties has finite classes, contradicting
  freeness of infinite `Q`.  Thus not only the one-coordinate attempt but
  the entire finite-valued normalizer ansatz is closed.  The surviving
  Mihailova route must use genuinely nonnormalizing Fourier coefficients and
  hence returns to the Hadamard-cell/full algebraic-envelope problem.
- **Nonnormalizing finite cells also fail inside the pure left-right host
  (proved, 2026-08-23).**
  `regular-kazhdan-reps-avoid-haagerup-crossed-products` removes every support
  and normalizer hypothesis.  An exact regular-character image of the
  infinite property-`(T)` quotient `Q` would generate a diffuse relatively
  rigid copy of `L(Q)`, whether or not `Q` is ICC.  Popa's relative-Haagerup
  theorem forbids such a subalgebra in an abelian crossed product by the
  Haagerup group `F_m times F_m`.  Consequently no finite Hadamard/matrix-cell
  assembly can represent `Q` inside the simplified left-right Bernoulli
  crossed product.  The caveat is exact and important: the full mixed actor
  `Gamma_0 times SL_3(Z)` is non-Haagerup.  A surviving Mihailova construction
  must use arithmetic grades outside the free left-right subgroup, or bypass
  a regular representation of `Q` and embed the fixed non-CE factor directly.
- **The arithmetic-grade survivor is one vertical coset wreath (proved,
  2026-08-23).**  `mihailova-sl3-restriction-is-coset-amplification` computes
  the restricted `SL_3(Z)`-set exactly:
  `(Gamma_0 times SL_3(Z))/P_Q` is a disjoint union, indexed by
  `Gamma_0/F_m`, of copies of `SL_3(Z)/N` with
  `N=ker(F_m->Q)`.  The free/Manzoor direction supplies only multiplicity.
  Then `mihailova-envelope-forces-one-sl3-coset-wreath` uses finite
  `SL_3`-module extraction and the diagonal embedding
  `(C^n rtimes SL_3) -> (C rtimes SL_3)^n` to show that a successful mixed
  envelope would already make the single group
  `(direct_sum_(SL_3/N) C_2) rtimes SL_3(Z)` nonhyperlinear.  The residual is
  now a named one-orbit arithmetic action: prove its generalized wreath group
  hyperlinear to kill the Mihailova route, or prove it nonhyperlinear to solve
  the group goal directly.
- **The GKP action-permanence test is sharp but the free restriction is
  vacuous (proved, 2026-08-23).**
  `mihailova-coset-wreath-sofic-action-boundary` applies GKP Theorem 3.8:
  soficity of `SL_3(Z) curvearrowright SL_3(Z)/N` would make the isolated
  wreath hyperlinear and kill the envelope route.  Restriction to the
  Mihailova subgroup cannot refute this hypothesis.  Its orbit is
  `F_m/N=Q`, but GKP Theorem 2.19 makes **every** free-group set action sofic,
  including this one when `Q` is finitely presented, property `(T)`, and
  nonsofic.  This gives an explicit failure of descent through the action
  kernel: the `F_m`-action is sofic while the factored regular `Q`-action is
  not.  Finite presentation merely makes `N` finitely normally generated,
  and a property-`(T)` kernel is impossible here because `N<F_m` is free and
  torsion-free.  Thus the residual really is the ambient arithmetic action;
  nonsoficity of that action would only block GKP, not prove the wreath
  nonhyperlinear.
- **A regular classical branch would force the vertical kernel separable
  (proved conditionally, 2026-08-23).**
  `orbitwise-relator-classicalization-separates-mihailova-kernel` gives the
  weakest direct profinite extraction currently visible.  If a hyperlinear
  model lifts the `SL_3(Z)` actor projectively at each level and the finite
  normal relators for `N=ker(F_m->Q)` act trivially on the **entire finite
  orbit** of the seed lamp observable, then that orbit is a finite
  `SL_3(Z)`-set with a point stabilizer containing `N`; the canonical lamp
  coefficient separates every `g notin N`.  Hence `N` is subgroup separable,
  contradicting the non-residual finiteness of `Q`.  Exact projective actor
  lifting supplies finiteness of the observable orbit by higher-rank
  superrigidity, but neither the SL3 projective trace-square transfer nor the
  Kac--Moody overlap machinery supplies whole-orbit relator triviality.  A
  zero-defect `S_3` permutation packet shows why fixing the seed alone cannot
  be upgraded by any HS constant: a relator can fix one branch while a
  conjugate moves it.
- **Finite lamp balls plus Kazhdan expansion still do not give orbitwise
  relator triviality (proved, 2026-08-23).**
  `sparse-relator-defects-defeat-orbitwise-classicalization` sharpens the
  preceding gate and corrects "entire orbit" to the weakest canonical clause,
  the `F_m`-orbit of the seed.  Over congruence quotients of the property-`(T)`
  group `SL_3(Z)`, take two regular orbits and cross-switch one edge of a
  redundant generator `z=w`.  The resulting exact free-group action is
  transitive, agrees with the quotient on any prescribed rooted word ball,
  and has relator defect density tending to zero, but `z w^(-1)` moves exactly
  two points.  Its binary Bernoulli matrices have exact actor covariance and
  exact pairwise lamp traces.  Since the orbit is transitive, deleting the
  two bad points has full invariant saturation: there is no positive
  invariant defect-free branch.  Thus property `(T)`/Poincare control cannot
  turn averaged relator triviality into the orbitwise clause; a genuinely
  global stability input is necessary.
- **One finite-dimensional coset coefficient is enough for hyperlinearity
  (proved conditionally, 2026-08-23).**
  `fd-fell-coset-observable-gaussianizes-wreath` isolates a strictly weaker
  observable than an invariant branch or a sofic action chart.  If the
  quasi-regular coefficient `1_N` is a pointwise limit of coefficients of
  finite-dimensional ambient `SL_3(Z)` representations, Gaussian signs turn
  their Gram matrices into all finite Bernoulli lamp moments.  The associated
  Gaussian actions have finite image by superrigidity; their crossed products
  are finite extensions of an amenable algebra tensored with a hyperlinear
  finite-index subgroup factor, hence CE.  A diagonal moment argument then
  makes the isolated coset wreath hyperlinear.  This coefficient condition
  does not imply separability: for a free actor surjecting onto a sofic
  non-residually-finite group it holds by freely extending permutation
  microstates, while the kernel is nonseparable.  The remaining arithmetic
  question is whether the specific coefficient `1_N` admits such
  finite-dimensional **ambient lattice** approximants; finite normal
  generation inside `F_m` and the sparse free-actor packets do not provide
  them.
- **The compact objects in Manzoor's primary construction do not already
  provide that envelope.**
  `manzoor-natural-subgroup-subshift-is-not-a-haar-envelope` audits the
  subgroup-indicator subshift, the finite pseudo-subgroup hierarchy, and the
  AGV labeled-Schreier realization.  `Sub(F)` is not an algebraic subgroup of
  `{0,1}^F` and is Bernoulli-Haar null.  Its conjugation stabilizer is
  `N_F(H)`, not `H`; more sharply, the strategy relators force
  `J in N_F(H) setminus H` almost surely, so the two stabilizer characters
  differ by `1` at `J`.  The LP optimizers have no compatible finite-action
  bonding maps, while AGV supplies only Haar fibers `[0,1]^(F/H)` over the
  unresolved base `mu`.  Thus there is no source-native compact-abelian Haar
  action to insert into `(AAE1)`.
- **Pontryagin-dualizing the additive measure algebra produces an explicit
  group, but the wrong trace.**
  `stone-additive-semidir-product-loses-manzoor-measure` forms
  `(A,symmetric_difference) semidirect F` from a countable invariant Boolean
  generator of a stabilizer action.  Its canonical event projections all
  have trace `1/2`, even when the original event has measure `1/3`.
  `stone-multiplicative-locus-is-haar-null-in-additive-dual` proves the Stone
  ultrafilters satisfying the intersection laws form a Haar-null set in the
  additive dual; moreover every central or `A`-reducing corner inside any
  containing group factor has Haar-absolutely-continuous spectral measure.
  Thus no nonzero corner selects the original probability algebra.  Enforcing
  the missing equations `p_(a meet b)=p_a p_b` is the nonlinear BCS
  groupification gate itself.
- **Fermionic second quantization consolidates the random fibers, but its
  groupifiable branch is exactly monomial.**
  `every-irs-character-is-an-exact-majorana-correlation` puts the
  quasi-regular direct integral into one real Hilbert space and obtains the
  exact bounded identity
  `tau(c(xi) U_g c(xi) U_g^*)=phi_mu(g)` in one Clifford crossed product.
  The returned Majorana commutators are still not multiplicative.
  `clifford-word-bogoliubov-groupification-is-signed-monomial` proves that
  the Bogoliubov action preserves a countable discrete Clifford word group
  exactly when the orthogonal representation is signed permutation in some
  basis.  Then the crossed product is the `z=-1` corner of
  `L(Cl_I semidirect Gamma)`; for the free Manzoor actor this group is
  amenable-by-sofic and hyperlinear.  Nonmonomial rotations remain analytic
  linear combinations of Majoranas and provide no canonical group words.
