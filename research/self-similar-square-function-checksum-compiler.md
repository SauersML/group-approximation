---
rg: 2
id: self-similar-square-function-checksum-compiler
kind: claim
title: Compile one finite relator into an orthogonal multiscale self-hash
distinct_from:
  common-source-orthogonal-partial-swap-star-compiler: that asks for two children at one scale and uses their product trace; this asks for one recursively nested carrier and one relator whose orthogonal blocks collect all scale syndromes.
  robust-locally-satisfiable-relator-code: that uses bounded-occurrence PCP checks across many sites; this asks for a single self-similar square-function word and a scalar martingale recurrence.
  finitely-presented-oligomorphic-linear-pauli-addresser: that compiles unbounded local test occurrences; this does not name occurrences and instead uses geometrically shrinking, orthogonal first-hit scale layers.
---

**OPEN.**  Construct a finite presentation `Gamma=<S|R>`, a nontrivial
involution `y`, and fixed constants

```text
0<lambda<1,       beta,C,K>0                           (SSC1)
```

with the following finite-matrix decoder.  Every sufficiently accurate
canonical-trace matrix model `U` supplies scalar carrier masses `a_n(U)` and
syndrome norms `s_n(U)` such that

```text
a_0(U)>=beta-o(1),                                    (SSC2)
a_n(U)<=lambda a_(n+1)(U)+C s_n(U)+o(1),             (SSC3)
sum_n lambda^n s_n(U)^2
 <=K sum_(r in R)||r(U)-I||_2^2+o(1).                (SSC4)
```

The `o(1)` terms must have a summable geometric envelope, so iterating
`(SSC3)` preserves a vanishing total modulus.  It is enough, and preferable,
that one fixed relator word `r_*` have orthogonal decoded first-hit blocks
`P_n` with

```text
s_n=||(r_*(U)-I)P_n||_2,                              (SSC5)
```

because Pythagoras then gives `(SSC4)` directly.

Exact completeness must give a representation with `y!=1`.  The decoded
finite scale chart is allowed to fail in that infinite representation; it
must use finite multiplicity, cyclic finite trace, or another genuinely
matrix-coordinate step.  Otherwise `(SSC2)--(SSC4)` would also kill the
marked carrier in the regular tracial representation.

The intended self-similar geometry is:

```text
root marked carrier
 -> persistent child plus first-hit exit
 -> repeat on the persistent child,
```

with the first-hit layers mutually orthogonal.  A late challenge can then be
rare, but it cannot be the only failure while the root remains macroscopic:
`(SSC3)` transports its geometric attenuation back to the root.  This is the
precise finite-presentation target left by the user's heavy-tail idea.

The recurrence `(SSC3)` is indispensable, not bookkeeping.
`orthogonal-checksum-controls-only-mass-weighted-syndromes` proves that one
perfectly authenticated Pythagorean word by itself controls only
`sum_n mu_n e_n`; a maximal late syndrome on a tiny block survives spectator
amplification.  The missing actuator must identify the blocks with the same
positive-mass reservoir strongly enough to prove `(SSC3)`.

## Self-similar host audit

- A pure faithful rooted-tree automorphism model cannot retain a mark only
  on the never-hit ray: `rooted-tree-first-hit-recursion-has-no-infinite-only-tail`
  proves that the recursion `g=(g,1,...,1)` gives `g=1`.  Such a
  level-preserving group is residually finite in any case.
- A contracting Nekrashevych host gives only finitely many deep section
  states for each fixed checksum word, by
  `contracting-self-similar-checksum-has-finite-deep-state`.  It can copy a
  fixed breaker but cannot manufacture unbounded capacity merely by going
  deeper.
- A literal Cuntz/Leavitt realization already contains the internal
  trace-cyclic corner or the external common-source swap star at level one,
  by `cuntz-first-hit-checksum-is-a-one-scale-corner`.  Its remaining gap is
  the existing matrix-only authentication of that first-level chart.
- Replacing scalar lamps by an infinite library of noncommuting packet labels
  does not by itself evade compactness.  By
  `noncommutative-checksum-misses-bounded-types`, any summable library of
  inequivalent packet representations of uniformly bounded dimension admits
  an equal-density two-type swap with arbitrarily small total covariance
  energy.  For a locally finite packet group,
  `locally-finite-checksum-misses-all-fd-types` removes even the dimension
  bound by aligning finite-subgroup multiplicity vectors after
  cross-amplification.  Thus translating or enlarging finitary
  Toeplitz/Schur heads through infinitely many addresses is still static
  compact data.  That lane must mix in a genuinely non-locally-finite tail,
  put the tests on orthogonal operator domains, and actually prove the
  backward carrier recurrence.
- There is a sharp positive noncommutative escape from this compactness wall.
  `kazhdan-generators-resolve-all-fd-types` proves that one finite Kazhdan
  generator packet controls the total transport among **all** inequivalent
  finite-dimensional isotypic components, with no dimension or type-count
  bound.  A property-(T) Toeplitz tail can therefore supply infinite type
  resolution once its action has been decoded exactly.  More precisely,
  `kazhdan-type-blocks-pack-a-square-function` partitions the pairwise
  orthogonal off-isotypic blocks of one router into arbitrary first-hit scale
  layers and bounds their complete square function by the same finite
  covariance energy.  Thus exact Kazhdan packet decoding solves the
  orthogonal packing clause `(SSC4)` with no depth union bound.  It still does
  not prove `(SSC3)`: the surviving construction problem is a genuinely
  non-Folner type-transition recurrence, rather than an infinite checksum
  library.  Ordinary tensor branching cannot supply it:
  `fixed-tensor-fusion-types-have-no-spectral-gap` proves that every finite
  family of normalized fusion operators on an infinite compact type space
  has remote finitely supported almost-invariant Peter--Weyl vectors.
  Replacing fusion by automorphisms still fails over any residually finite
  packet: `rf-packets-have-finite-marked-automorphism-orbits` finds a finite
  characteristic quotient, invariant under the whole actor, which retains
  every prescribed nontrivial mark.  Thus the remaining recurrence must use
  a finite-residual mark, a genuinely proper endomorphism, or a matrix-only
  proper corner.
  Even the proper-endomorphism option cannot live on a finite-rank abelian
  packet: `abelian-matrix-hnns-have-marked-finite-quotients` reduces any
  finite family of injective integer matrices modulo one prime where all
  become automorphisms and the mark survives.  A surviving endomorphism
  actuator must be nonabelian or infinite-rank and defeat every common
  mark-detecting finite quotient.
  Finite-rank free packets do not provide an easy nonabelian escape either:
  every single injective endomorphism has compatible marked finite quotients
  by `single-free-endomorphism-has-marked-finite-quotients`, and every finite
  family with full-rank rational abelianization shares a characteristic
  finite pro-`p` quotient by
  `full-h1-rank-free-endomorphism-families-periodize`.  The remaining free
  case requires at least two branches and a singular-`H_1` endomorphism.
  Nonabelian nilpotent packets do not repair the recurrence:
  `nilpotent-endomorphism-families-have-periodizations` proves that every
  finite family of injective endomorphisms of a finitely generated
  torsion-free nilpotent packet acts by automorphisms on one common finite
  `p`-group quotient retaining any prescribed mark.
- A noncontracting Baumslag--Solitar clock also does not supply the checksum
  from spectral recurrence alone.  By
  `periodic-bs-clock-defeats-spectral-first-hit-checksum`, exact finite
  doubling-permutation models have arbitrarily long one-atom first-hit
  layers, zero local relator defect, and Haar limiting marginals.  Cyclically
  gluing four edges does not repair this at the marginal level:
  `split-higman-cycle-has-haar-marginals-and-maximal-role-gap` gives exact
  split edge models whose repeated roles have identical limiting moments but
  asymptotically maximal Hilbert--Schmidt discrepancy.
- Adding one unlocalized mixed holonomy word does not repair that defect.
  `one-product-holonomy-does-not-sew-four-bs-clocks` alternates exact clock
  mismatches `P_q` and `P_q^(-1)`, so the product holonomy is exactly trivial
  while all four occurrence gaps remain macroscopic.  A viable one-word
  compiler must therefore make the scale syndromes positive/orthogonal;
  ordinary unitary product cancellation is fatal.
- Replacing the clock by the binary parity substitution
  `q c q^-1=c(h c h^-1)`, `q h q^-1=h^2` still does not expose the
  individual syndrome layers.  `dyadic-parity-checksum-has-finite-pauli-gauge`
  gives an exact finite nine-cycle extraspecial model in which every iterated
  block-parity check holds but distance-two lamps anticommute by the central
  mark.  A successful square function must authenticate individual first-hit
  blocks, not merely their recursively commuting parities.

Therefore the genuinely new possibility left by `(SSC1)--(SSC5)` is a
noncontracting or matrix-coordinate square-function decomposition which is
visible as one finite word without functorially decoding a Cuntz family in
the regular representation.  In a Higman-type host it must be a genuinely
joint eigenbasis-holonomy or common-occurrence estimate; a scalar spectral
first-hit ledger or bare product holonomy is insufficient.
