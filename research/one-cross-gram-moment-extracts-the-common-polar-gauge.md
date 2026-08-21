---
rg: 2
id: one-cross-gram-moment-extracts-the-common-polar-gauge
kind: claim
title: One cross-Gram moment extracts a common polar gauge from two packet transports
distinct_from:
  gowers-hatami-uniqueness-does-not-lock-nested-pauli-reservoirs: that shows separate fixed-level intertwiners retain arbitrary multiplicity gauges; this gives the exact extra scalar overlap which turns two transports into one relative gauge.
  two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge: that forces an already exposed gauge into the smaller child commutant; this constructs that gauge and aligns the two transport words.
  eight-slice-capacity-deficit-is-one-overlap-moment: that compares source and target projection capacities; this is an abstract intertwiner lemma for two packet-compressed paths and uses their cross-Gram operator.
---

Let `(M,tau)` be a finite tracial von Neumann algebra.  Let `p,q in M` be
projections, let `alpha:G -> U(pMp)` and `beta:G -> U(qMq)` be exact
representations of one fixed finite packet, and let

```text
T_1,T_2 in q M p                                           (CGP1)
```

be contractions satisfying the exact intertwining equations

```text
T_i alpha(g)=beta(g)T_i  for every g in G and i=1,2.       (CGP2)
```

These are the packet-compressed forms of two transport words with the same
source and target packet corners.

### One-moment common-gauge lemma

Put

```text
R=T_2^*T_1 in pMp,
Delta=tau(p)-tau(R^*R)
     =tau(p)-tau(T_1^*T_2T_2^*T_1).                       (CGP3)
```

Then `Delta>=0`, and there is a unitary

```text
V in alpha(G)' cap pMp                                    (CGP4)
```

such that

```text
||R-V||_2 <= sqrt(Delta),                                 (CGP5)
||T_1-T_2V||_2 <= sqrt(2 Delta).                          (CGP6)
```

Thus a **single scalar cross-Gram moment** within `Delta` of full source mass
produces one common relative polar gauge and aligns the two transport words.
The constants are independent of matrix dimension, packet multiplicity, and
the size of the target corner.

### Proof

Taking adjoints in `(CGP2)` shows

```text
R alpha(g)=alpha(g)R,                                     (CGP7)
```

so `R` belongs to the finite von Neumann algebra
`N=alpha(G)' cap pMp`.  It is a contraction.  Let `R=W|R|` be its polar
decomposition inside `N`.  The initial and final support projections of `W`
have the same center-valued trace in `N`; finiteness therefore lets us extend
`W` to a unitary `V in N`.

On the singular values of `R`,

```text
(1-s)^2 <= 1-s^2  (0<=s<=1).
```

Consequently

```text
||R-V||_2^2
 =tau((p-|R|)^2)
 <=tau(p-|R|^2)=Delta,                                   (CGP8)
```

which is `(CGP5)`.

For the aligned transports, use `R^*V=|R|` and contractivity:

```text
||T_1-T_2V||_2^2
 =tau(T_1^*T_1)+tau(V^*T_2^*T_2V)-2 Re tau(T_1^*T_2V)
 <=2tau(p)-2tau(|R|)
 <=2(tau(p)-tau(|R|^2))
 =2Delta.                                                 (CGP9)
```

This proves `(CGP6)`.  Notice also that

```text
tau(T_i^*T_i)>=tau(R^*R)>=tau(p)-Delta,                   (CGP10)
```

so the one cross-Gram hypothesis automatically forces both compressed paths
to be almost isometric on the common source corner.  No separate two-sided
Gram assumptions are needed.

### Interface with Gowers--Hatami uniqueness

Gowers--Hatami supplies exact partial intertwiners after fixed-packet
exactification, but two independently obtained intertwiners may have
different source/range supports.  The hypotheses needed before applying the
lemma are exactly:

1. a packet projection `p` selected **before** separating the two paths;
2. one target packet corner `q` containing both compressed ranges;
3. exact intertwining on the exactified packet, after discarding the usual
   `O(epsilon^2)` exceptional mass; and
4. the single overlap estimate in `(CGP3)` on those common corners.

Under these hypotheses, `(CGP4)--(CGP6)` produce the same polar gauge for the
two paths.  Applying
`two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge` to the two
child-return discrepancies then forces this `V` into
`I_2 tensor U(m_(n+1))`.

Equivalently, if the two paths agree after transport on the child `X` and `Z`
words, `(CGP6)` turns those two comparisons into small commutators of the one
common `V`; the two-moment gauge lock completes the tensor-inclusion
compatibility.

### Minimal countermodel when the overlap moment is absent

Let `alpha` be any packet representation on `pH`, and let

```text
beta=alpha direct_sum alpha                                (CGP11)
```

on a target corner of twice the dimension.  Let `T_1,T_2` be the two
orthogonal coordinate embeddings.  They satisfy `(CGP2)` exactly and are
exact isometries with the same source packet, but

```text
T_2^*T_1=0,
tau(T_1^*T_2T_2^*T_1)=0.                                 (CGP12)
```

There is no relative unitary `V` for which `T_1` is close to `T_2V`; their
ranges are orthogonal.  This is the smallest rectangular countermodel to
common-gauge extraction.  Gowers--Hatami uniqueness applied to each path
separately does not see the missing cross-Gram overlap.

### Claim boundary and regular firewall

The lemma is valid in every finite tracial von Neumann algebra.  It proves
that **one** overlap scalar is sufficient after the source and target corners
have already been identified.  It does not force that scalar to be large.

Forcing `(CGP3)` by a universal tracial identity may also force it in the
regular representation, so the overlap estimate itself must come from the
source-specific matrix/non-CE input or from a finite-multiplicity capacity
argument that is legal in the exact infinite witness.  Producing two large
self-Gram moments without the cross-Gram moment is insufficient by
`(CGP11)--(CGP12)`.  The remaining compiler target is therefore precisely
one common-corner cross-Gram lower bound, not a family of compatible polar
choices.

`localized-non-ce-leakage-forces-cross-gram-overlap` now gives the precise
matrix-ultraproduct mechanism for a positive overlap.  Gram capacity says
that orthogonal exits must leak outside the fixed target capacity; the finite
localized Fanizza moment matrix on each leakage projection then invokes the
corner non-CE gap and forbids BCS-quiet leakage.  Source-only moments cannot
do this, because orthogonal bookkeeping-coordinate embeddings preserve them
exactly.  The remaining compiler estimate is the mixed localization bound
making the actual leakage ranges approximately reducing and residual-free
for the same shared Fanizza tuple.
