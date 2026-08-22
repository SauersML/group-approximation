---
rg: 2
id: atlas-augmented-rank-zero-set-compactness
kind: claim
title: Promote an augmented Atlas rank-ultraproduct point to a finite matrix zero
distinct_from:
  sublinear-bandwidth-is-vacuous-under-rank-amplification: that removes the apparent band restriction; this is the resulting unrestricted rank-metric compactness problem.
  atlas-block-circulant-joint-escape-promotes-to-exact-mode: fixed-block circulants have residue-field evaluations which prove this promotion in that special commutative class.
  atlas-exact-matrix-zero-set-is-a-finite-quotient-test: that starts with an exact finite matrix zero; this must produce one from an exact point only in a rank ultraproduct.
  growing-rank-decoder-is-linear-soficity: that classifies the ultraproduct point as a linear-sofic representation but supplies no finite-coordinate exactification.
---

OPEN.  Let `E_+` be the finite matrix Laurent system consisting of the
repeated natural-module Atlas packet, collision `19243`, and q14, with its
two faithful marked `A8` charts.  Prove:

```text
there exist m_n -> infinity and T_n in GL_(2m_n)(F2)
with max_(R in E_+) rank R(T_n)/m_n -> 0

                    implies

there exist finite m and T in GL_(2m)(F_(2^f))
with R(T)=0 for every R in E_+.                       (ARC1)
```

Restriction of scalars would make the conclusion an exact binary model, and
the established exact-zero/finite-quotient reduction would then give a
nontrivial finite quotient of the augmented Atlas group.

The hypothesis of `(ARC1)` is exactly an exact faithful-chart point in a
rank-metric matrix ultraproduct.  Coordinatewise direct and stable finiteness
do not prove the conclusion: they preserve one-sided inverse identities in
the ultraproduct but do not lift a general finitely presented algebra
homomorphism to an exact finite-dimensional representation.  Thus `(ARC1)`
is a genuine rank-zero-set compactness/rank-stability statement, not a
consequence of direct finiteness.

By `sublinear-bandwidth-is-vacuous-under-rank-amplification`, adding
`bandwidth(T_n),bandwidth(T_n^-1)=o(m_n)` leaves `(ARC1)` unchanged.  This is
the precise missing theorem for the width-growing noncirculant stitching
lane.

## Attempts

- **Primary Fourier quotients stop at circulants.**  The fixed-block cyclic
  proof has a common central shift and finite residue-field modes.  An
  arbitrary band tuple has no commuting translation algebra, and diagonal
  amplification makes its relative bandwidth vanish without creating one.
- **Stable finiteness is too weak.**  Rank ultraproducts satisfy
  `rank(1-AB)=rank(1-BA)` coordinatewise, but the Atlas system is not a lone
  one-sided-inverse equation.  This identity supplies no exact finite
  coordinate or finite quotient.
- **Finite-section compactness needs uniform propagation.**  A fixed-radius,
  finite-alphabet one-dimensional constraint can be passed to a periodic
  model.  Here the permitted width grows, and amplification realizes every
  unrestricted rank microstate inside that regime.  Invoking such a compactness
  argument would therefore assume `(ARC1)` rather than prove it.
- **The quotient is not itself a graph of finite groups.**
  `atlas-augmented-thirteen-vf-fillings`
  presents it as a virtually free carrier filled by twelve independent cycle
  stable letters and the hyperbolic collision word.  Residual finiteness of
  the carrier does not descend through this multiple filling, and the
  collision misses the available relative small-cancellation threshold.
- **Published rank stability stops before both required operations.**
  `atlas-rank-stability-literature-fence`
  source-checks the normalized-rank literature.  Finite-dimensional
  `F_2`-algebras and their ordinary free products are flexibly rank-stable,
  so the individual Atlas charts can be corrected.  No audited theorem
  synchronizes those corrections across nontrivial finite-edge amalgams, and
  no theorem preserves rank stability under the thirteen finite-relator
  fillings.  Schatten stability and p-adic ultrametric stability of virtually
  free groups use different metrics and do not fill this gap.
- **The two observed phases are separated but path-connected.**
  `atlas-m2-kernel-phases-have-rank-path-barrier` gives normalized rank
  separation `1/32` from each pure amplified phase to the opposite zero
  stratum, yet also connects those phases inside the packet-zero locus by
  rank-eight steps.  The canonical path pays a linear joint residual.  The
  unresolved invariant is the full-stratum density statement
  `atlas-full-kernel-strata-rank-separation`, not topological disconnectedness.
- **Mixed fixed-space charges are rank pencils, not a lift.**
  `atlas-mixed-fixed-spaces-are-rank-pencils` writes every proposed
  `dim(Fix_K intersect T^-1 Fix_L)` exactly as the nullity of a degree-one
  rectangular pencil.  These values pass continuously to the rank
  ultraproduct and have growing denominators, so no finite-profile
  pigeonhole extracts an exact coordinate.  They remain viable only as a
  source of a universal Sylvester-rank contradiction or after a relative
  correction theorem for the packet.
- **There is no formal rank-zero compactness principle.**
  `rank-zero-compactness-fails-for-invertible-laurent` gives invertible
  rational matrices with rank-one defect for `VUV^-1U^-1=2I`, although the
  determinant excludes every nonzero finite exact solution.  This is not a
  characteristic-two counterexample to `(ARC1)`; it proves that any proof of
  `(ARC1)` must exploit special Atlas structure rather than ultraproduct
  exactness plus a finite relation list.
- **The binary residual is wandering defect propagation.**
  `atlas-defect-orbit-span-quotient-dichotomy` takes the images of the
  augmented residual matrices and closes them under the two exact repeated
  natural `A8` chart actions.  If that orbit-span is proper, its quotient is
  automatically an exact finite augmented model with faithful repeated
  charts.  Hence any counterexample to `(ARC1)` with no finite escape must
  spread an `o(m)` defect seed onto the entire carrier through alternating
  chart words of unbounded depth.  It is enough to prove a dimension-free
  orbit-span bound or saturation depth for this specific thirteen-relation
  system.  This is the precise binary error-delocalization statement left
  after the mixed-rank-pencil and literature fences.
- **Fixed-block companion/shift wandering is still cyclic.**
  `atlas-low-rank-cyclic-perturbations-promote` proves that Laurent residuals
  change by at most a fixed word-length multiple of `rank(T-S)`, including
  inverse letters.  Hence any companion or finite-section gauge differing
  from an invertible fixed-block cyclic closure in `o(m)` rank falls under
  the existing cyclic primary-mode theorem and produces an exact finite
  zero.  A symbolic wandering construction must therefore use growing block
  width, a singular cyclic closure, or stay a positive normalized-rank
  distance from every fixed-block circulant.
- **A singular cyclic closure does not rescue a fixed formal symbol.**
  `atlas-fixed-formal-toeplitz-microstates-promote` treats multiplication by
  one `B(z) in GL_b(F2[[z]])` on the truncations modulo `z^N`.  Evaluation of
  every Laurent relation is still a ring homomorphism, including the global
  triangular inverse.  Any nonzero formal residual has rank at least `N-O(1)`,
  so sublinear residuals make the formal symbol an exact solution.  Zariski's
  lemma then produces an exact point over a finite extension of `F2`.
  Consequently a symbolic wandering construction must have growing
  block/state width or genuinely nonstationary coefficients; neither an
  invertible nor a singular fixed-width companion symbol can evade finite
  specialization.
- **The finitely presented algebra has infinite one-sided width.**
  Put `P=F2[A8*A8]` and let `I` be the augmented relator ideal.
  `atlas-augmented-relator-ideal-not-left-finite` proves that `I`, although
  finitely generated as a two-sided ideal, is not finitely generated as a
  left `P`-module.  The reason is exact: the Bass--Serre kernel is a free
  group of infinite rank, and a group-algebra quotient kernel is
  left-finitely-generated exactly when the kernel subgroup is finitely
  generated.  Thus no bounded algebraic list of relator translates can
  control the wandering space.
- **Exact remaining module statement.**
  `atlas-left-ideal-rank-nonwandering` asks whether, on modules restricting
  to `V^m` on both charts, low normalized rank of the thirteen named ideal
  generators forces the full ideal image `I E` to have sub-full (ideally
  vanishing) normalized dimension.  The quotient dichotomy turns that
  statement directly into `(ARC1)`.  A countermodel is precisely a sequence
  with a vanishing-rank named seed but `I E=E`; the fixed-width theorems force
  any such sequence to use growing state width or nonstationary data.
- **Ordinary Bass--Serre Folner truncations miss the marked face.**
  `atlas-edge-folner-modules-miss-natural-type` gives a fixed modular rank
  obstruction: a transvection has normalized `rank(t-I)=1/2` on the free
  chart orbits forming the bulk of an edge-induced graph module, but value
  `1/4` on every repeated natural chart.  Boundary changes of `o(m)` rank do
  not close that gap.  Hence the infinite chart-coset graph does not itself
  supply a countermodel; one needs positive-density nonfree chart cells whose
  relation errors cancel by a mechanism beyond ordinary Folner compression.
