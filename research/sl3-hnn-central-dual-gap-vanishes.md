---
rg: 2
id: sl3-hnn-central-dual-gap-vanishes
kind: claim
title: Stable-letter-central dual tuples have no positive SL3 matrix-range separation gap
distinct_from:
  sl3-large-prime-hnn-matrix-range-capture: that is the primal assertion that the selected lattice tuple approaches the ucp matrix range; this is its strictly restricted dual form after central-letter averaging, quantifying only over uniformly bounded separators asymptotically commuting with the HNN letter.
  hnn-matrix-range-obstruction-is-a-letter-multiplicity-coupling: that proves a positive-gap separator must live off the intrinsic spectral algebra; this is the open arithmetic assertion that even the remaining multiplicity-commutant separator has nonpositive gap.
  single-hecke-average-isometry-for-lambda-central-unitaries: that tests one primal lattice-central unitary under one fixed arithmetic Hecke average; this tests every bounded dual generator tuple in the stable-letter commutant against the support function of the full group matrix range.
---

Fix `p>=11` and the data `Lambda`, `Gamma`, `G_p`, `S` of
`sl3-large-prime-hnn-matrix-range-capture`.  Let
`phi_n:G_p->U(d_n)` be a canonical hyperlinear approximation, put
`X_(n,s)=phi_n(s)` and `T_n=phi_n(t)`, and write

```text
h_n(B)=sup_(Y in MR_(d_n)(Lambda,S))
       Re sum_(s in S)tr_(d_n)(B_s^*Y_s).                         (LCG1)
```

For every tuple sequence `B_n=(B_(n,s))_s` satisfying

```text
sum_s||B_(n,s)||_2^2=1,
sup_(n,s)||B_(n,s)||_op<infinity,
sum_s||T_nB_(n,s)T_n^*-B_(n,s)||_2^2 ->0,                         (LCG2)
```

the claim is

```text
limsup_n [ Re sum_s tr_(d_n)(B_(n,s)^*X_(n,s))-h_n(B_n) ] <=0.    (LCG3)
```

By `central-letter-averages-matrix-range-separators`, `(LCG3)` implies
`sl3-large-prime-hnn-matrix-range-capture`: any positive primal distance
would yield a uniformly operator-bounded tuple obeying `(LCG2)` with a
fixed positive gap, contradicting `(LCG3)`.  Thus this is the smallest
currently isolated UCP lemma closing the large-prime HNN route.  It no
longer asks to correct an arbitrary lattice microstate, or even to test all
dual directions; it asks only that the stable-letter commutant contain no
positive matrix-range separator for the selected lattice tuple.

There is an equivalent endpoint with no ultraproduct quantifier:
`sl3-hnn-finite-window-central-dual-gap`.  For each operator-norm cutoff and
target gap it asks for one finite canonical trace window and one tolerance
forcing the support inequality in every matrix dimension.  The two
diagonalization routes prove equivalence.  In particular, the remaining
outlier question is a uniform finite matrix-range inequality, not an
inherently infinitary strengthening of weak ucp-stability.

## Attempts

- `hnn-matrix-range-obstruction-is-a-letter-multiplicity-coupling` removes
  the intrinsic `W^*(T)` part: a positive-gap tuple must have definite
  off-spectral mass in `T' cap M`.  Hence scalar Fourier analysis of the
  Haar letter cannot settle `(LCG3)`.
- **The one-letter multiplicity/Choi conversion is exactly neutral.**
  `letter-central-matrix-range-separation-is-morita-neutral` shows that,
  after finite-order rounding of `T`, both the support function and the gap
  split as weighted sums over the spectral multiplicity blocks.  Conversely
  every ordinary gap amplifies beneath an asymptotically Haar central letter
  with the same off-spectral mass.  This invalidates
  `sl3-central-dual-via-letter-multiplicity-stinespring`: blockwise
  Stinespring actors presuppose the ucp points whose existence is the claim.
  Any positive proof must use the S-arithmetic extension, concretely a
  coupling between the `T` blocks and the conjugate-letter blocks of
  `phi(h)Tphi(h)^*`, not the commutant of `T` alone.
- **Two conjugate letters plus the overlap still do not couple the Choi
  cones.**  `two-conjugate-letter-overlap-data-is-morita-neutral` uses
  finite regular quotients of `C_k*Z` to realize arbitrary canonical windows
  of `T` and `phi(h)Tphi(h)^*`, while tensoring an arbitrary separator on a
  common `C=Lambda cap hLambda h^(-1)` multiplicity actor.  The gap is
  unchanged.  This invalidates
  `sl3-central-dual-via-two-letter-iwahori-blocks`.  Therefore the exact
  surviving arithmetic datum is narrower: one must use the nontrivial
  transport by `phi(h)` of the full endpoint generators outside `C`, not
  merely the two spectral block systems, their canonical pair moments, or
  their common Iwahori actor.
- **Even a canonical full-endpoint finite actor is Morita-neutral.**
  `endpoint-matched-amplification-is-matrix-range-neutral`
  proves an exact support-function identity for the matched amplification
  `X_s -> v(s) tensor X_s`, `B_s -> v(s) tensor B_s`.  The proof compresses
  the contragredient tensor by a maximally entangled vector.  Thus a finite
  representation of the entire S-arithmetic base may carry every transport
  `v(h lambda h^(-1))=v(h)v(lambda)v(h)^*`, and residual-finite regular
  actors may make any fixed base-word window canonical, without decreasing
  a separator gap.  This invalidates
  `sl3-central-dual-via-canonical-full-endpoint-amplification`.  The usable
  input is narrower still: the canonical **mixed Britton-word** moments
  tying the stable-letter multiplicity to the base actor, not canonical
  base moments or full endpoint transport in a separate tensor factor.
- **A fixed quasiregular lamp frame is still neutral.**
  `finite-lamp-frame-is-matrix-range-neutral` realizes every prescribed
  finite collection of reduced words in the conjugates
  `phi(a)Tphi(a)^*` by a finite regular quotient of `C_k*F_q`, and tensors
  an arbitrary separator through the frame with its support function and
  gap unchanged.  This invalidates
  `sl3-central-dual-via-finite-lamp-frame` and strengthens the moving-window
  firewall: even all noncommutative cross-Grams in one fixed lamp window
  do not help.  The surviving mixed moment must retain **actor covariance**:
  the same arithmetic matrices must permute the lamp frame and transport
  the lattice coordinates.  After forgetting that common actor, Britton
  reduction leaves only a Morita-neutral free-lamp law.
- **Actor covariance is exactly the coset-action soficity fork.**
  `centralizer-hnn-is-free-generalized-wreath` identifies the full group as
  `Z wr^*_(Gamma curvearrowright Gamma/Lambda) Gamma`.  By
  `sofic-coset-action-refutes-sl3-central-dual`, a sofic atlas for this
  coset action produces canonical finite-coordinate enemies and forces
  `(LCG3)` to fail.  Therefore proving `(LCG3)` necessarily proves that the
  large-prime type-zero building-vertex action is nonsofic.  The remaining
  task is no longer “add more mixed moments”: it is a matrix-order
  obstruction to every coherent finite atlas for that action, or an
  equivalent specifically arithmetic failure of actor/lamp covariance.
- **Exact arithmetic action atlases are uniformly excluded at every prime.**
  `sl3-prime-permutation-codensity` makes the integral stabilizer profinitely
  dense in the full S-arithmetic actor, and
  `sl3-prime-coset-action-exact-atlas-firewall` combines this with the
  Kazhdan gap to put every exact finite-action atlas a fixed Hamming distance
  away.  Therefore neither subgroup separability, congruence actions, nor
  unlabelled finite building quotients can produce the actor-covariant
  enemy.  But this is a fence, not `(LCG3)`: a sofic model, if one exists,
  must be a genuinely noncorrectable coherent approximate deck-cocycle
  atlas.  Ruling out precisely those outliers is the remaining dynamical
  obstruction.
- **The permutation fork reduces to stability in finite actions, not full
  flexible P-stability.**
  `sl3-prime-stable-finite-actions-excludes-coset-soficity` proves that the
  weakest standard modulus presently available already kills every positive
  coset atlas: weak containment of sofic-approximation limits in finite
  actions contradicts the exact Kazhdan/co-density atlas gap.  This is still
  open for `SL_3(Z[1/p])`; current quotient-inheritance results require a
  normal Kazhdan kernel and do not apply to the nonnormal integral lattice.
  Thus the actor-covariant enemy is now reduced to one named permutation
  stability statement, but no published theorem supplies it.
- Property T cannot act directly on `B_n`: the lattice tuple is still an
  almost-representation, while `B_n` centralizes the stable letter rather
  than a genuine lattice representation.  Producing a Stinespring actor at
  this point would already prove the desired matrix-range inequality.
- The weighted Rayleigh no-go
  `balanced-leak-saturates-weighted-rayleigh-tests` concerns one scalar
  coefficient of a primal projection.  Here `h_n(B)` is a complete-matrix-
  order support function; the missing datum is a host relation forcing its
  multiplicity-commutant component to pay.
- On the near-genuine face `(LCG3)` follows from the established exact-face
  collapse at `p>=11`.  Therefore any counterexample is simultaneously a
  uniform lattice outlier and a bounded nonabelian stable-letter-
  multiplicity Choi separator.  No existing arithmetic type decomposition
  applies before that outlier is exactified.
