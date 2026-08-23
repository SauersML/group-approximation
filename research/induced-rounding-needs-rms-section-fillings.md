---
rg: 2
id: induced-rounding-needs-rms-section-fillings
kind: claim
title: Induced relative rounding reduces the moving basin to RMS section fillings
distinct_from:
  fixed-level-bs14-compatible-basin: that compares the shadow error with an abstract finite-level stability radius; this constructs the natural induced-representation repair and identifies one explicit quantitative statistic sufficient for crossing.
  repeated-squaring-and-tau-do-not-supply-the-moving-basin: that proves a generic short-presentation and expansion firewall; this locates the missing two-dimensional quantity inside the special exact-core induction construction.
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that rounds inside one already authenticated endpoint orbit; this uses induction to formulate the prior relative lift from an exact core into some endpoint type.
  authenticated-core-union-basin-is-relative-liftability: that identifies the qualitative flexible lifting endpoint; this supplies one quantitative sufficient construction in terms of Schreier-section fillings and an exact finite induced representation.
  cyclic-core-character-forces-linear-rms-section-area: that refutes the required sub-square-root RMS bound, even on authenticated regular cores, while leaving gauge-optimized flexible repair open.
  gauge-optimized-induced-energy-target: that replaces the refuted frozen-core estimate by minimization over nearby exact BS core coordinates.
---

Let `A_N` be one finite one-power Iwahori quotient, let `B_N<A_N` be
the image of the exact BS core, and let

```text
beta:B_N -> U(H)                                      (IRF1)
```

be exact.  Suppose a unitary tuple `U` extends `beta` on the presentation
generators up to maximum normalized-HS defect `delta`.  Fix a right-coset
section `T_N` for `A_N/B_N`.  For every presentation generator `a` and
`t in T_N`, write the exact Schreier transition

```text
a^(-1)t=t' b,       t' in T_N, b in B_N,             (IRF2)
```

and let `A_N(t,a)` be the minimum relative van Kampen area proving the
corresponding section-word identity, with exact `B_N` identities charged
zero.  Put

```text
M_N=max_a ((1/|T_N|) sum_(t in T_N) A_N(t,a)^2)^(1/2).
                                                               (IRF3)
```

There is a canonical isometry

```text
V_U:H -> Ind_(B_N)^(A_N)(beta)                       (IRF4)
```

whose generator-intertwining defect is at most

```text
max_a ||rho_N(a)V_U-V_U U(a)||_(2,H) <= M_N delta.   (IRF5)
```

Here the norm is Frobenius normalized by `dim(H)`, not by the much larger
induced dimension.  If the finite quotients have one uniform Cayley
spectral gap `kappa>0`, `(IRF5)` and conditional expectation round the range
projection `V_U V_U^*` to an `A_N`-invariant projection with relative
Frobenius displacement `O_kappa(M_N delta)`.  Its rank is

```text
dim(H)+O((M_N delta)^2 dim(H)),                       (IRF6)
```

and its compression gives a flexible exact endpoint at generalized distance
`O_kappa(M_N delta)` from `U`.

Consequently this induced-representation strategy would cross the regular
dyadic shadow of level `N=4^K-1` if it supplied sections with

```text
M_(4^K-1)=o(sqrt(K)).                                 (IRF7)
```

Ordinary path length or Cayley expansion does not imply `(IRF7)`.  Expansion
only bounds the one-dimensional section lengths by `O(log|A_N|)=O(K)`;
relator-by-relator telescoping sees the **relative 2-cell fillings** in
`(IRF3)`.  Thus the induction idea does not remove the missing theorem: it
rephrases it as sub-square-root RMS section filling, or as a stronger
square-function/cocycle-expansion inequality replacing the area triangle
bound.

The exact energy-level replacement needed for the flexible boundary theorem
is especially concise.  If `D_U(t,a)` denotes the coordinate edge defect in
the proof of `(IRF5)` and

```text
E_R(U)=sum_(r in R) ||r(U)-1||_2^2,
```

then a uniform inequality

```text
max_a (1/|T_N|) sum_t ||D_U(t,a)||_2^2
 <= C E_R(U)                                           (IRF8)
```

would, after the same spectral-gap rounding, give relative padding
`O(E_R(U))` and displacement `O(sqrt(E_R(U)))`.  This is exactly the
quadratic padding scale in
`bs14-flexible-cross-packet-boundary-reconciliation`.  Hence `(IRF8)` is a
finite relative two-dimensional expansion/cochain-filling theorem which
would close the flexible boundary step; one-dimensional property `(tau)`
only performs the subsequent projection rounding.

This is a sufficient reduction and a proof-method firewall.  It does not
by itself assert that the special Iwahori sections fail `(IRF7)`.
`cyclic-core-character-forces-linear-rms-section-area` now proves the sharp
negative answer: every section has `M_(4^K-1)>=cK`.  It also refutes the raw
fixed-core energy estimate `(IRF8)`.  The counterfamily is nevertheless
`O(1/K)` from an exact endpoint after moving the core, so the surviving
target must optimize continuous core coordinates before forming the induced
section, or use a gauge-optimized two-dimensional energy rather than frozen
relative fillings.

The precise corrected functional and its reduction to flexible repair are
recorded in `gauge-optimized-induced-energy-target`.  The minimization there
is over the full exact finite-level core variety; quotienting only the
explicit scalar character is not enough because exact BS packets also carry
slow commutant modes.
