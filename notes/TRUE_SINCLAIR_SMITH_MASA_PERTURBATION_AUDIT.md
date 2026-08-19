# Sinclair--Smith gives the normalizer correction, not the common masa

Date: 2026-08-11

Source: Allan M. Sinclair and Roger R. Smith,
*Unitary perturbations of masas in type II1 factors*,
[arXiv:math/0111330](https://arxiv.org/abs/math/0111330).

## Outcome

This paper supplies an exact, dimension-free correction theorem at one of
the TRUE interfaces.  If a unitary already almost preserves a specified
masa in the conditional-expectation norm, then it is close in normalized
`L^2` norm to a unitary normalizing that masa.  In a finite atomic masa, the
normalizer is the monomial group, so this is precisely a
unitary-to-monomial rounding statement once the common masa has been found.

It does **not** construct a common approximately invariant masa from an
arbitrary hyperlinear table.  It also does not remove the diagonal phases of
the resulting monomial matrices.  Thus it closes the correction *after* the
Cartan gate, but not the Cartan gate or the fixed-phase gate themselves.

## 1. The exact perturbation theorem

Let `A` be a masa in a separably acting type-`II_1` factor `N`, let `E_A`
be the trace-preserving conditional expectation, and let `N(A)` denote the
unitary normalizer.  Sinclair--Smith Theorem 5.3 states that for every
unitary `u in N`,

```text
d_2(u,N(A))/31
 <= ||(I-E_(uAu^*))E_A||_(infinity,2)
 <= ||E_A-E_(uAu^*)||_(infinity,2)
 <= 4 d_2(u,N(A)).                                  (SS1)
```

Here

```text
||Phi||_(infinity,2)=sup_(||x||<=1)||Phi(x)||_2.     (SS2)
```

Consequently, if

```text
||E_A-E_(uAu^*)||_(infinity,2)<=epsilon,             (SS3)
```

then there is `v in N(A)` with

```text
||u-v||_2<=31 epsilon.                               (SS4)
```

The theorem is not a compactness assertion: the constant `31` is universal.
Its published scope is separably acting type-`II_1` factors.  Any use in
finite matrix algebras must either invoke a finite-dimensional analogue or
justify an amplification without losing the required atomic normalizer.
For the finite atomic application in this repository,
`TRUE_CARTAN_MONOMIAL_GATE.md` already supplies a direct matrix proof with a
better average-atom estimate.

## 2. The large-corner coherence theorem

The paper contains a second result that is potentially useful for gluing
local Cartan data.  If `A,B` are masas and

```text
||E_A-E_B||_(infinity,2)<=epsilon,                   (SS5)
```

then Theorem 5.4 produces projections `p in A`, `q in B` and a unitary `z`
such that

```text
z^*qz=p,
z^*qBz=pA,
tr(p)=tr(q)>=1-24 epsilon^2,                         (SS6)
||z-E_B(z)||_2<=(25/2+2 sqrt(24)) epsilon.           (SS7)
```

Thus close masas agree, after a controlled gauge, on a corner whose lost
mass is quadratic in their distance.  This is stronger than merely finding
one nearby normalizing unitary and is the correct published tool if a future
construction first produces vertex masas whose transported copies are
edgewise close.

It still begins with the masas.  Neither `(SS1)` nor `(SS6)` extracts an
abelian algebra from the multiplication and trace defects of a general
matrix microstate.

## 3. Comparison with the repository's atomic estimate

For the diagonal masa `D subset M_d(C)`, put

```text
kappa_D(U)
 =sum_j ||Up_jU^*-E_D(Up_jU^*)||_(2,d)^2
 =1-d^(-1)sum_(i,j)|u_(ij)|^4.                       (SS8)
```

The Birkhoff argument in `TRUE_CARTAN_MONOMIAL_GATE.md` gives a monomial
unitary `M` satisfying

```text
||U-M||_(2,d)^2<=2 kappa_D(U).                       (SS9)
```

This estimate is directly adapted to normalized average atom error and is
dimension-free.  Sinclair--Smith instead assumes the stronger operator-map
quantity `(SS3)`.  Therefore the paper does not improve `(SS9)` for the
actual finite-matrix norm used here.  Its value is conceptual and
structural:

```text
approximate preservation of a supplied masa
        => exact normalizer after small L^2 correction,                (SS10)

closeness of two supplied masas
        => exact conjugacy on a 1-O(epsilon^2) corner.                  (SS11)
```

## 4. Exact interface with the `A_3(F_q)` metric cone

The metric cone theorem in `TRUE_A3_METRIC_CONE_SYNCHRONIZATION.md` repairs
an almost-flat connection in any group carrying a conjugation-invariant
subadditive length.  If a `U(d)` connection `U_e` is already attached to one
common masa `D` and satisfies `(SS3)` edgewise, then `(SS4)` first replaces
each edge by a normalizer of `D`; on an atomic `D` these are monomial edges.
The metric cone theorem can then synchronize their monomial holonomy with
constants independent of `d` and `q`.

This is a valid two-stage pipeline:

```text
common almost-invariant masa
  --Sinclair--Smith / atomic Birkhoff--> monomial connection
  --A_3 metric cone--> synchronized monomial connection.              (SS12)
```

But it is conditional on the first phrase.  An arbitrary hyperlinear model
does not come with such a masa, and examples already recorded in the
notepad show that abstract Connes embeddability need not preserve a chosen
Cartan algebra.

## 5. Why this still does not prove TRUE

Two independent obstructions remain.

1. **Common-masa construction.**  One must obtain a single atomic masa (or a
   finite-window substitute) from the normal-`0/1` trace law and the word
   defects.  Sinclair--Smith assumes this object rather than constructs it.

2. **Fixed-point phases.**  A normalizer of an atomic masa is monomial, not
   necessarily a permutation.  Diagonal phases on permutation-fixed points
   can cancel the matrix trace.  The tensor-power `C_4` example in
   `TRUE_CARTAN_MONOMIAL_GATE.md` has the regular `0/1` limiting character
   while every underlying permutation is the identity.  No masa
   perturbation estimate can remove this phase obstruction by itself.

Hence the paper is a strong positive component, but not the missing global
rounding theorem.  The sharp reusable conclusion is:

> Once a common approximately invariant masa is available in the
> conditional-expectation metric, normalizer/monomial correction is already
> quantitatively solved with a universal constant; the real open work is to
> construct that masa coherently and then control the fixed phases.

## 6. Relation to the positive-commutant endpoint

The later finite-Fourier calculation in
`FALSE_POSITIVE_COMMUTANT_CHARACTER_MATCHING.md` should not be replaced by
Sinclair--Smith.  There the positive subgroup representation is already
exactly diagonalizable, and conditional expectation onto its commutant plus
polar correction gives a dimension-free correction from an approximately
commuting unitary to an exact commutant unitary.  The exact marked optimum is
then a finite assignment problem inside character-restriction fibers.

Sinclair--Smith concerns approximate **normalization of a masa**, while that
endpoint concerns approximate **commutation with an abelian representation**.
Neither implies the other in the form needed here, and the elementary
commutant correction has the sharper hypotheses for the endpoint.  The
paper therefore remains assigned only to the Cartan-to-monomial interface;
it does not improve the newly solved local positive-commutant bound.
