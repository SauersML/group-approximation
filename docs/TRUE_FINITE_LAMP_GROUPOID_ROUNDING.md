# Finite lamp groupoids round once their object partitions exist

Date: 2026-08-13

## 1. The finite diagram

This note records the multi-object version of
`TRUE_FINITE_REGULAR_NORMALIZER_ROUNDING.md`.  It is the exact form needed by
a finite word-prefix attack on the Kun--Thom group.

Let `O` be a finite set of objects.  At each object `o` suppose the same
finite-dimensional Hilbert space has an equal-rank decomposition

```text
1 = sum_(i in I_o) p_(o,i),
rank(p_(o,i))=r,             |I_o|=m.                 (FGR1)
```

For every arrow `e:o->o'`, prescribe a bijection

```text
alpha_e:I_o -> I_(o')                                      (FGR2)
```

and a unitary `U_e`.  Define its block-transport defect by

```text
eta_e^2 = sum_(i in I_o)
  ||U_e p_(o,i) U_e^* - p_(o',alpha_e(i))||_2^2.       (FGR3)
```

All Hilbert--Schmidt norms are normalized by the ambient matrix dimension.

## 2. Simultaneous arrow rounding

**Theorem 1.**  Every arrow has an exact block transport `V_e` satisfying

```text
V_e p_(o,i) V_e^* = p_(o',alpha_e(i)),
||U_e-V_e||_2 <= eta_e.                               (FGR4)
```

If `e:o->o'`, `f:o'->o''`, and `h:o->o''` are named arrows, then

```text
d_H(alpha_f alpha_e,alpha_h)
 <= (1/2) (
      ||U_f U_e-U_h||_2 + eta_f+eta_e+eta_h
    )^2.                                               (FGR5)
```

**Proof.**  Apply dimension-free block polar rounding separately to every
arrow to obtain `(FGR4)`.  The product `V_f V_e` has block map
`alpha_f alpha_e`, whereas `V_h` has block map `alpha_h`.  On a source block
where these maps disagree, the two images are orthogonal, contributing
`2r/d` to their squared normalized Hilbert--Schmidt distance.  Therefore

```text
2 d_H(alpha_f alpha_e,alpha_h) <= ||V_f V_e-V_h||_2^2.
```

The triangle inequality and unitary invariance give

```text
||V_f V_e-V_h||_2
 <= ||U_f U_e-U_h||_2+eta_f+eta_e+eta_h,
```

which is `(FGR5)`.  End proof.

There is no requirement that the decompositions at different objects agree.
The only compatibility needed for composition is that the target partition
of `e` is literally the source partition of `f`.

## 3. Linear quantization

Suppose every label set is a finite vector space over `F_2` and every
`alpha_e` is linear.  Two distinct linear maps disagree on at least half the
label set.  Consequently, if the right side of `(FGR5)` is strictly below
`1/2`, then

```text
alpha_f alpha_e = alpha_h                              (FGR6)
```

exactly.  For a fixed finite multiplication table, sufficiently accurate
unitary coherence therefore produces an exact linear groupoid table.

This discrete assertion is formalized in
`GroupApproximation/Sofic/FiniteLinearHammingGap.lean`.

## 4. Application to finite lamp windows

For a finite lamp subgroup `B_Y=(C_2)^Y`, a regular-multiple representation
has its equal-rank Fourier partition indexed by `B_Y^`.  If an arrow `g`
intertwines `B_Y` with `B_(gY)`, Fourier Parseval identifies `(FGR3)` with

```text
(1/|B_Y|) sum_(b in B_Y)
  ||U_g rho(b) U_g^* - rho(gbg^(-1))||_2^2.            (FGR7)
```

Thus the hyperlinear covariance relations provide precisely the hypothesis
of Theorem 1 after the two finite subgroup restrictions have been rounded to
regular multiplicity.

For a fixed finite family of word paths, this yields exact label transports
between all *available* object partitions, and composition is automatically
exact once the errors cross the `1/2` threshold.  In particular, internal
unitaries inside high-multiplicity regular blocks and independent choices of
polar factors do not create a cocycle obstruction at label level.

## 5. The remaining object-completion gate

The theorem deliberately does not manufacture the object set `O`.  Taking
objects to be the finitely many translated lamp windows along tested word
prefixes gives a finite partial groupoid, but quotient generators can carry a
boundary object outside that set.  Completing those object arrows coherently
is equivalent to producing the missing finite model of the coset action.

Flexible stability of finite permutation groupoids starts *after* one has an
approximate action on a single finite object set.  It does not turn a finite
collection of non-invariant windows into that object set.  Likewise, applying
amenable conversion separately to the cyclic groups

```text
B semidirect <g>
```

chooses unrelated bases for different quotient generators; aligning those
bases coherently is the same object-completion problem.

Hence the local analytic part of the word-prefix proposal is now closed:

```text
regular object partitions
  + unitary covariance
  + unitary word coherence
    ==> exact finite linear groupoid labels.            (FGR8)
```

The unresolved step is purely global: construct a common finite object model
from the pointwise ultraproduct lamp action without assuming a Folner or
profinite approximation of `G/Gamma`.

## 6. Information audit: labels alone cannot perform the completion

For the translated subgroups `B_(gY)`, the label bijections in `(FGR2)` are
the canonical duals of the algebraic maps `b |-> gbg^(-1)`.  They are
therefore determined by the original coset action and contain no information
specific to the hypothetical hyperlinear matrices.  A procedure which
completed the object set using only these canonical label maps would construct
a finite approximation of the Kun--Thom action without using hyperlinearity at
all.  That is exactly what their nonsoficity theorem rules out.

The matrix-specific information discarded by passage to `alpha_e` consists
of the unitaries acting inside the regular multiplicity blocks.  Consequently
a valid nonhyperlinearity proof must do one of two things:

1. use coherence of those internal block unitaries to force a forbidden
   object completion; or
2. show that every attempted coherent internal system has a uniform
   normalized-Hilbert--Schmidt defect.

Simply invoking `(FGR8)` and then completing the canonical partial action is
circular.  The groupoid rounding theorem closes the local analytic losses,
but it also pinpoints where the genuinely quantum data still has to enter:
the multiplicity-block holonomy around the finite prefix diagram.
