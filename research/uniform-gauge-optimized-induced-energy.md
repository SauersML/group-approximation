---
rg: 2
id: uniform-gauge-optimized-induced-energy
kind: claim
title: Uniform induced edge energy after optimizing the exact BS core
distinct_from:
  gauge-optimized-induced-energy-target: that defines the optimized functional, proves its sufficiency, and checks the scalar counterfamily; this is the still-open assertion that the functional is uniformly bounded by presentation energy.
  induced-rounding-needs-rms-section-fillings: that freezes the input core and is false uniformly; this permits every nearby exact core before forming the induced section.
  gauge-optimized-target-has-uniform-congruence-tangent-gap: that proves the linearization of this statement on the locally exact congruence tangent slice; this asks for its global nonlinear normalized-HS form.
---

With `G_N` and `E_end` defined in
`gauge-optimized-induced-energy-target`, prove that one constant `C` works
for every dyadic level `N=4^K-1`, every dimension, every exact level-`N`
BS core `b`, and every involution `X`:

```text
G_N(X,b) <= C E_end(X,b).                              (UGO1)
```

Flexible padding may be included in the competitors in `G_N`, with its
relative rank charged as an additional nonnegative term.

The congruence tangent quotient has a uniform gap, so `(UGO1)` has no
moving-level infinitesimal obstruction.  Its content is nonlinear
integration in normalized HS after quotienting the complete exact-core
variety.

## Attempts

- Frozen-core induction is false: the `r`-exponent character gives constant
  section energy from `O(K^(-2))` relator energy.  Optimizing the exact core
  absorbs this family at the correct scale.
- The stronger endpoint-conjugation counterpacket which refutes aggregate
  Iwahori inverse energy is also absorbed exactly. For
  `X_z=zXz^(-1)`, choose the competitor core
  `(zRz^(-1),T)`. The hybrid tuple is a conjugate exact endpoint, so its
  section energy is zero; the core-motion cost is
  `||z-psi(z)||_2^2`. On the first-mode left regular family this is at most
  `16 E_end` for sufficiently small amplitude. See
  `optimized-core-absorbs-endpoint-conjugations`.
  Infinitesimally, the apparently bad frozen-core endpoint tangent
  `a-Ad(X)a` is paired with the core tangent
  `(a-Ad(R)a,0)`. Together they are precisely a common-conjugation tangent
  removed in `(GIT1)`, explaining why the gauge-only and frozen-core full
  tangent gaps can decay while the optimized quotient gap does not.
- The complete one-sided exact-core normal slice is globally coercive with
  no basin hypothesis.  If `(X,R,T)` is exact and an arbitrary
  `q in {T}'` changes the supplied core to `(qR,T)`, then, writing

  ```text
  u=(XqR)^2,                 v=(XT^2qR)^3,
  ```

  `optimized-core-one-sided-normal-slice-is-exactly-coercive` proves the
  exact identity `||q-1||_2=||v-u||_2` and consequently
  `G_N(X,(qR,T))<=2E_end(X,(qR,T))`.  This excludes operator-large,
  small-rank, and torsion-multiplicity escapes on every core motion which
  keeps the root generator and endpoint fixed.  A surviving obstruction
  must move outside this slice: it must jointly change the represented root
  generator/endpoint type or fail to admit a common exact baseline.
  In particular, once `(X,T)` has any exact endpoint completion, the same
  estimate holds for every exact BS implementer over `T`; the choice of a
  wrong implementer is no longer an obstruction.
- The implementer fiber is controlled even before such a completion is
  authenticated.  `fixed-root-exact-core-fiber-has-pairwise-row-coercivity`
  proves that for any two exact cores `(R_i,T)` under one fixed involution,

  ```text
  ||R_1-R_0||_2^2<=4(E_(inv,second)(R_0)+E_(inv,second)(R_1)).
  ```

  Hence separated row-tame wells cannot occur inside a fixed-root fiber;
  only the root/endpoint coordinate can carry the remaining basin failure.
  More generally, if two same-stratum roots can be aligned by a unitary in
  `{X}'`, the conjugated implementers obey the same constant-four bound.
  Such an alignment cannot be selected from the row energy alone.
  `x-central-root-alignment-fails-inside-one-exact-stratum` gives two exact
  congruence endpoints under one common `X`, with identical root spectral
  multiplicities and zero row energies, whose roots stay uniformly apart
  modulo `{X}'`.  Thus the within-stratum survivor is not any subsequent
  implementer correction, but adaptive selection of the full endpoint type
  (or a comparison which moves `X` and the root simultaneously).
- More globally, `exact-bs-core-strata-have-conjugation-commutant-normal-form`
  proves that every fixed root-multiplicity stratum of `C_N(d)` is exhausted
  by common conjugation followed by exactly the one-sided slice above.  If
  the involution follows the conjugation coordinate, `(UGO1)` again holds
  with constant two on the whole stratum.  Therefore a genuinely transverse
  counterexample must mismatch the involution from that transported exact
  endpoint orbit or cross root-multiplicity strata; there is no third
  nonlinear core coordinate hidden inside a stratum.
- A preliminary invariant rank-paid reconciliation of different root
  strata is impossible.  `bs-root-strata-have-no-energy-paid-invariant-reconciliation`
  gives exact `m`-dimensional cores in distinct irreducible strata whose
  squared HS distance is `O(1/m)`, while making their exact BS types equal
  by invariant padding costs at least another `m` dimensions.  Thus the
  fixed-stratum constant-two theorem cannot be globalized by packet cutting
  with `rank/d=O(E)`.  A positive stratum theorem must move the comparator
  core directly/non-invariantly, which `(GOI4)` permits, and charge that
  motion jointly to the Iwahori rows.  On every even packet length, the same
  pair fails the exact Iwahori determinant fence, so it cannot itself be
  promoted to a packetwise UGO counterexample; any true stratum escape must
  occur inside a larger coupled congruence restriction atom.
- A valid two-transport overlap mechanism is now available, but starts after
  a missing authentication step.  If two contraction transports into one
  target have cross-Gram mass `m>0`,
  `two-transport-cross-gram-has-a-fixed-mass-reducing-corner` extracts a
  source corner of trace at least `m/2` with explicit packet-commutator
  bound; an authenticated congruence commutant gap makes it exactly reducing.
  `lin-cross-gram-localizes-authenticated-iwahori-overlap`
  records why Lin's state-local finite-group dilation does not itself supply
  `(UGO1)`: the raw core can have infinite-order `R`, the other Iwahori
  vertex is a left rather than opposite action and is Reynolds-twirled, no
  second transport or overlap floor is supplied, and the amplification has
  no energy-proportional rank bound.  Thus the `X`/orbit survivor is narrowed
  to producing positive-overlap transports before this conditional corner
  theorem can fire.  Even then, the exact cuspidal-redistribution family
  shows that a fixed regular reference recovers at most its common
  `1/2+o(1)` summand; the zero-defect complement must be assigned an adaptive
  moving endpoint type rather than discarded.
- Ordinary HS Newton integration is unavailable because operator-large
  rank-one directions have no dimension-free quadratic Taylor remainder.
- Spectral thresholding isolates the operator-large residual on rank
  `O(E/theta^2)`, but its BS-invariant hull can have full packet rank.
  Therefore the active carrier must be paired and reconnected through the
  two cubic polar ranges without first taking an invariant hull.  This is
  the reverse active-dilation problem in
  `bs14-residual-polar-data-build-active-dilation`.
