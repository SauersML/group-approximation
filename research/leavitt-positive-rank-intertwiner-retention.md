---
rg: 2
id: leavitt-positive-rank-intertwiner-retention
kind: claim
title: Retain a positive-rank almost-quotient sector in the Leavitt presentation double
distinct_from:
  shulman-double-forces-unstable-kernel-restriction: that produces operator-norm unstable pairs; this asks for a trace-visible almost-reducing sector inside their left-right representations.
  shulman-presentation-double-witnesses-have-adjoint-normal-form: that chooses the unstable pairs in one globally conjugate Julia normal form and identifies the exact zero-energy sector; this still asks for positive spectral bands with trace-visible self-normalized rank.
  mf-trace-gap-defect-ratio-models: that asks for a global dimension-versus-defect profile in arbitrary MF models; this asks for a quotient-specific spectral compression and renormalizes by the retained sector's own dimension.
  unnamed-fixed-space-promotion-is-goal-equivalent: that warns that promoting a single almost-fixed vector to macroscopic ambient rank is goal-equivalent; this permits a small ambient sector but requires approximate invariance relative to its own normalized rank.
  free-presentation-kernel-has-no-conjugation-folner-exhaustion: that rules out making a weighted kernel energy equivariant by a normality-only Folner choice of its word coefficients; this still permits representation-specific cancellation or a moving spectral-band construction.
  finite-kernel-window-has-maximally-moving-zero-mode: that gives every fixed kernel window an exact finite-dimensional zero mode moved orthogonally by `f_0`; this requires a genuinely growing window coupled to relative-rank almost reduction.
  hall-reflection-realizes-rank-one-restriction-instability: that realizes all bare restriction-instability and Julia-normal-form hypotheses on one vanishing-rank coset reflection; this must use additional simultaneous-word structure of the faithful double model.
  finite-cross-word-family-fits-one-hall-reflection: that concentrates every fixed finite family of canonical cross-word gaps on one rank-one reflection; this must use longer alternating-word coupling or genuinely all-word structure rather than a larger finite cross-word list.
  sublinear-julia-seam-collapses-the-fold-kernel-tracially: that shows even arbitrary alternating fold-kernel words remain trace-null whenever the Julia seam has sublinear rank; this must establish rank spreading or escape the seam's principal rank ideal.
  julia-derivation-rank-controls-fold: that proves macroscopic `rank(V-1)` is pure commutant gauge and identifies normalized generator-commutator rank as the necessary trace-spreading datum; this still asks to turn that datum into one almost-quotient band satisfying all three IR clauses.
  leavitt-presentation-double-fd-radical-is-fold-kernel: that proves every honest finite-dimensional representation of the entire double factors through the fold; this asks for a genuinely asymptotic band that cannot be repaired to such an exact representation.
  shulman-presentation-double-has-a-faithful-fold-trace-model: that proves even faithful operator-norm coordinates for the whole double can have the completely folded limiting trace; this asks for a separately selected trace-visible spectral band.
  leavitt-presentation-double-has-all-fold-mf-moments: that constructs canonical-marginal symmetric MF traces with every ordinary fold-word moment, including zero; this asks for the different compressed adjoint moment on an IR1--IR2 sector.
  ir-survival-is-one-compressed-adjoint-moment: that rewrites IR3 as one scalar compressed trace gap once IR1--IR2 hold; this remains the open construction of a sector on which that scalar and both structural conditions hold together.
---

**OPEN.** Fix a finite free presentation

```text
Q=F/K=EL_4(L_(F_2)(1,2))
```

There exist a choice of exact representation pairs `u_n,v_n` witnessing
`shulman-double-forces-unstable-kernel-restriction` and nonzero subspaces as
follows. On
`H_n=HS(C^(d_n))`, put

```text
Pi_n(f)(T)=u_n(f)T v_n(f)^*.
```

Find nonzero subspaces `W_n<=H_n`, with projections `P_n` and
`r_n=dim(W_n)`, such that norms below are normalized by `r_n` and:

```text
(IR1) ||(1-P_n)Pi_n(f)P_n||_(2,r_n) -> 0  for every fixed f in F;
(IR2) ||(Pi_n(k)-1)P_n||_(2,r_n) -> 0      for every fixed k in K;
(IR3) liminf ||(Pi_n(f_0)-1)P_n||_(2,r_n) > 0
      for some f_0 notin K.                                  (IR)
```

An exact `F`-invariant, `K`-trivial sector cannot work:
`simple-map-quotient-has-rigid-fd-restriction` would make its quotient action
trivial. The required sector must therefore remain genuinely asymptotic.

The low-energy spectral projection of

```text
A_(n,m)=sum_(j<=m)(Pi_n(k_j)-1)^*(Pi_n(k_j)-1)
```

is the natural candidate, but the known almost-invariant vector
`I/sqrt(d_n)` controls only one spectral direction. The missing statement is
relative-rank control together with `(IR1)` and survival `(IR3)`; neither
operator-MF nor the exterior-power amplifier supplies it automatically.

There is no exact-representation endpoint hidden behind this spectral
problem.  The theorem
`leavitt-presentation-double-fd-radical-is-fold-kernel` says that every
honest finite-dimensional representation of `P=F *_K F` factors through the
fold `P->F` and therefore kills every marked cross word.  Hence correcting a
candidate band to an exact representation of the **double** would destroy
`(IR3)`.  The live object must be non-exactifiable at each finite stage, not
merely a poorly chosen exact block.

Nor does norm faithfulness of the full Shulman coordinate sequence choose the
needed trace.  The theorem
`shulman-presentation-double-has-a-faithful-fold-trace-model` constructs a
faithful MF model of the whole amalgam whose normalized traces converge to
the folded free-group trace and hence kill every fold word.  Thus retention
must be imposed by additional trace data; selecting "the" trace of a
faithful Shulman embedding is not a well-defined refinement.

Even prescribing the ordinary marked fold moment does not supply that data.
The continuum theorem `leavitt-presentation-double-has-all-fold-mf-moments`
constructs faithful, swap-symmetric MF models with canonical vertex
marginals and any chosen value of `tr(u(f_0)v(f_0)^*)`, including the
canonical value zero.  The exact surviving scalar is instead `(CAM1)` of
`ir-survival-is-one-compressed-adjoint-moment`: the normalized trace of
`Pi_n(f_0)` on the **same** almost-reducing, almost-`K`-trivial sector.

The refinement
`shulman-presentation-double-witnesses-have-adjoint-normal-form` shows that
the pairs may be chosen as `u_n=V_n^* sigma_n V_n`, `v_n=sigma_n`.  Under
left multiplication by `V_n`, `Pi_n` is exactly `Ad(sigma_n)`, and

```text
Fix(Ad(sigma_n)(K))=Fix(Ad(sigma_n)(F)).
```

Thus an exact zero-energy cutoff can only produce the trivial quotient
action.  The live spectral candidate is a band of **positive** kernel energy
whose upper endpoint tends to zero; Shulman's Julia construction gives no
rank or multiplicity bound for such a band.

The word *positive-rank* here means positive rank after normalizing on the
retained sector; no positive fraction of the ambient `d_n^2` dimensions is
assumed. In fact `(IR1)--(IR3)` force `r_n` to be unbounded after passage to a
subsequence: bounded `r_n` would give a nontrivial honest finite-dimensional
representation of `Q` by compactness, contrary to
`simple-map-quotient-has-rigid-fd-restriction`.

The Hall-reflection calibration shows why all three clauses must be checked
on the **same** band.  Its exact zero-energy line already has `(IR1)` and
`(IR2)` while its operator-visible fold defect has vanishing normalized
displacement, so `(IR3)` alone fails.  Spectral-flow or moving-cutoff
arguments must therefore prove trace-visible survival in addition to
equivariance; the latter cannot promote the operator wall by itself.

Nor is it enough merely to add longer alternating words.  The Julia rank
firewall `sublinear-julia-seam-collapses-the-fold-kernel-tracially` proves
that one low-rank implementer makes every fixed word in the **entire** fold
kernel tracially null.  But `rank(V_n-1)` itself cannot be the sought lower
bound: commutant gauges change it without changing either vertex map, and
`V=-1` has full deviation rank while moving no word.  The intrinsic target
from `julia-derivation-rank-controls-fold`
is positive normalized rank of the generator commutators
`[sigma_n(x),V_n]`.  A successful moving-band argument must convert that
active support into `(IR1)--(IR3)`, or find trace-visible positive-energy
motion outside it; finite-word norm faithfulness alone does neither.
