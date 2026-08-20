---
rg: 2
id: one-sided-paired-frame-reverse-reservoir-collapse
kind: claim
title: A one-sided compressor makes the paired frame's 011 escape nonreturning
artifacts:
  - experiments/schur_packet_paired_commutant_frame.py
distinct_from:
  compressor-covariant-packet-reynolds-return: that asks for the final dimension-free payment for every contextual forbidden core; this is the remaining word-level placement theorem for the single explicit 101-to-011 escape of one support packet.
  full-center-hnn-transport-cancels-schur-multiplicity: that exhibits stationary regular flow through a finite full-center graph; this requires an infinite one-sided orbit whose reverse carriers cannot form a stationary cycle.
  support-packet-paired-word-frame-exposes-forbidden-rank: that constructs and classifies the two finite frames; this must place their four named generators in the compressed/full Kazhdan commutants and control the orbit boundary.
---

Construct a fixed finitely presented group gadget containing a Kazhdan subgroup
`Lambda`, a strict one-sided compressor `s`, and the source/coefficient support
packets of `support-packet-paired-word-frame-exposes-forbidden-rank`, with the
following properties.

1. The four plus frame words lie in the commutant of `s Lambda s^-1`, while
   the four minus frame words describe the corresponding full-`Lambda`
   commutant coordinates.  These placements are consequences of named group
   relators and fail in the tensor-decoupled model.
2. After finite-packet exactification, scaled Kazhdan transport has only the
   finite-edge escape classified in `(PWF3)`: forbidden `101` mass may move to
   a reverse `011` carrier, with all other loss charged to a bounded-overlap
   relator energy.
3. Iterating `s` puts successive reverse carriers in pairwise orthogonal
   prefix/level corners.  For every depth `N`, if `q_0` is the initial `101`
   carrier mass and `E` is the named relator energy, then

```text
N q_0 <= 1 + C p(N) sqrt(E),                           (PRC1)
```

   for a fixed polynomial `p` and dimension-independent `C`.  Equivalently,
   after exponential weighting in the Fanizza ladder the reverse reservoir is
   contractive and cannot return stationary mass to the initial packet scale.
4. The exact non-CE tracial model is retained: its contextual support has no
   `101` mass, so the oriented frame relations introduce no contradiction in
   the completeness model.

Together with the fixed frame rank jump, `(PRC1)` makes every positive
forbidden carrier pay uniform normalized-HS energy.  The load-bearing point is
literal orthogonality (or an equally strong summable overlap bound) of the
successive `011` carriers; merely assigning them different names recreates the
regular Bass--Serre reservoir.

## Current coordinates

- The two coefficient shears in `(PWF1)` are
  `p_1 -> p_1 p_2` and `q_1 -> q_1 q_2`.  They are the same elementary
  transvection shape already present in Cairn's raw-compressor/comb atlas.
- The finite search is complete: there are 32 symbolic frame isomorphisms and
  every one sends `101` to `011`.  No additional finite character reservoir
  needs to be controlled.
- `paired-frame-hard-characters-form-forced-two-cycle` sharpens this: every
  one of the 32 maps also sends `011` back to `101`.  Thus changing or
  alternating finite edge isomorphisms can never orient the hard pair; an
  infinite label is mandatory.
- `alternating-free-ring-shears-have-strict-degree-drift` supplies a concrete
  label.  The product of the two elementary `F_2[x]` shears has leading degree
  `2n` at its `n`th iterate.  Coupling the forced two-cycle to this action
  returns the finite character after two steps but moves it to a new degree.
- The most literal implementation of that idea is false.
  `paired-frame-fixed-kernel-polynomial-clock-no-go` proves that the stationary
  paired-edge kernel admits only four one-directional square-zero polynomial
  shears and no opposite pair.  A degree-growing transporter must carry the
  kernel through the orbit `K_n=wedge^2(T^n)K_0`, rather than stabilize `K_0`.
- The moving-kernel calculation is exact and favorable.
  `paired-frame-moving-kernel-is-a-rank-one-veronese-clock` proves
  `K_n=K_fixed direct_sum L_n`, where the fixed core has rank two and the
  pairwise-distinct `L_n` are lines with leading degree `4n-2`.  Thus the
  required atlas moves precisely one relative relation coordinate and no
  higher multiplicity space.
- `paired-hard-form-transverse-to-moving-clock` identifies
  that coordinate with the Boolean detector itself: the hard form is
  `e_02^*`, and its value on `L_n` is the nonzero polynomial `c_n^2` of
  leading degree `4n-2`.
- The kernels cannot be installed as one normal polynomial module.
  `normal-closure-of-moving-kernels-kills-the-hard-form` proves that their
  cumulative span has rank five and leaves only
  `e_03^*+e_12^*`; the hard covector is lost.  The moving coordinate must
  therefore be separated by spectral corners/sites, not merely conjugated as
  global relations.
- One-sided transport supplies exactly that separation: keep the coefficient
  packet fixed and transport only the source packet.  The combined relation
  kernel at level `n` is then `K_0 intersect K_n=K_fixed`, not the normal
  closure of all `K_n`.  Its commutator matrix has Smith invariants
  `(1,1,1,c_n,0,0)`, where `c_n=(S^n)_(21)` is monic of degree `2n-1`.
  Thus the entire rank jump is one additive-character phase at a fresh top
  coefficient, with no arbitrary corner projection.
- `e5-heisenberg-word-realizes-rank-one-boundary-pulse` installs this
  comparison in honest group words.  The four frame roots sit in the
  `(2,1,2)` Heisenberg block of `E_5(F_2[x])`, and the four-letter elementary
  word `D=diag(S,1,S^-1)` transports only the source copy.  On the relative
  hard character its `n`th pulse has the unique top coefficient
  `e_13^* x^(4n-2)`, so the corresponding Fourier boundary contains exactly
  one Pauli bit.
- On dyadic iterates `n=2^k`, the stronger
  `dyadic-e5-hard-pulses-have-disjoint-degree-bands` puts the whole pulse in
  `[2n-1,4n-2]`; these intervals are adjacent and pairwise disjoint.  Thus no
  polynomial tail from a later selected iterate leaks into an earlier degree
  reservoir.  Spectral first-hit localization is still needed because one
  additive character can be nontrivial on several bands.
- `free-root-top-boundary-reservoir-is-summable` proves the required capacity
  theorem for those degree labels: the mass first detected at successive
  degrees telescopes and has total at most one on a unit carrier.  Literal
  prefix projections are therefore optional; identifying each emitted hard
  character with the corresponding top-degree Fourier layer is enough.
- `corner-localized-non-ce-bcs-energy-gap` proves that BCS violation mass
  cannot dilute after cutting to an approximately reducing prefix carrier,
  even when that carrier has vanishing ambient trace.
- `first-hit-carrier-contraction-ladder` isolates the exact remaining
  accounting.  It suffices to preserve one baseline carrier copy, emit a
  fixed fraction of its trace into a new reverse carrier, and make those
  reverse carriers orthogonal.  The resulting trace budget is `(PRC1)`.
- `free-root-first-detection-eigenvectors-localize-exactly` proves the
  packet-to-reservoir analytic endpoint: once a hard intertwiner has
  coefficient-character valuation `n`, its entire squared norm is exactly
  the `n`th boundary mass.
- The word-level realization and exact valuation calculation are now closed.
  The missing step is quantitative persistence of the baseline relative-Pauli
  module under approximate conjugation: after exactifying each finite root
  stage, the hard intertwiner must retain a fixed fraction of its mass until
  it emits into the `4n-2` boundary, with only polynomial word error.  Once
  this estimate is proved, localization and boundary summability give `(PRC1)`.
  A merely decreasing first-hit process is insufficient: it admits a
  geometric reservoir and does not force collapse.
