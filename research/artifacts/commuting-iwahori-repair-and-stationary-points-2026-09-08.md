# A constructive commuting control and stationary near-compatible points

2026-09-08. This answers two different questions about the polynomial
Iwahori correction. A genuine endpoint can be constructed on the jointly
commuting subclass, with quadratic normalized-rank cost. Yet the smooth
least-squares gradient vanishes at every point of that subclass, even at
noncompatible points arbitrarily close to compatible points in their own
torsion stratum. No general flexible stability conclusion is asserted.

## 1. Exact repair from the finite character support

Let all four matrices `S_1,B_1,S_2,B_2` commute jointly, and assume the
exact modular relations `S_i^4=I`, `S_i^2=B_i^3`. Thus `B_i^6=I`.
They are commuting normal matrices, so choose one common diagonal basis.
Every diagonal generator value, and therefore every scalar word value,
is a twelfth root of unity. Distinct such roots have distance at least

```text
g=2sin(pi/12)>0.
```

Write the three Iwahori word differences as `R_1,R_2,R_3`, and use
the normalized HS Hilbert tuple norm `e^2=sum_j ||R_j||_2^2`.
The positive matrix `T=sum_j R_j^*R_j` is diagonal. Let

```text
P=1_((0,infinity))(T),        r=rank(P).
```

This is the exact common spectral support of the residuals. Each
coordinate in its range contributes at least `g^2` to the unnormalized
trace of `T`. Consequently

```text
r/n <= e^2/g^2.                                      (1)
```

All four generators commute with `P`. Define

```text
S_i'=(I-P)S_i+P,       B_i'=(I-P)B_i+P.               (2)
```

On `P` both vertices are trivial; on its complement all three original
compatibility equations already hold. Both modular relations and all
Iwahori equations therefore hold exactly for (2). This constructs a
compatible representation in dimension `n`, using the input residuals
only. For each generator `U`,

```text
rank(U'-U)<=r,
||U'-U||_2<=2sqrt(r/n)<=2e/g.                         (3)
```

No common reducing space was guessed: the joint commutation hypothesis
makes the displayed spectral support reducing. Without that hypothesis,
the support of the residual need not reduce either vertex, and (2) is
not a legitimate general repair. Separate commutation within each
vertex, with no cross-vertex commutation, is insufficient for this proof.

## 2. Every jointly diagonal pair is stationary in the exact charts

Use the natural chart of
[the modular parameterization proof](modular-vertex-admissible-charts-2026-09-08.md).
At zero parameter, its generator derivatives have the form

```text
dS=[H_0+H_4,S],       dB=[H_0+H_6,B].                 (4)
```

For every matrix `H` and diagonal matrix `D`, the diagonal of `[H,D]`
is zero. Thus (4) has zero diagonal, even when directions mix distinct
joint eigenspaces. The derivative of a word is a sum of products of
diagonal matrices and one such zero-diagonal matrix. Its diagonal is
again zero. The inverse-generator terms have the same property.

Let `F` be the residual in these charts, `f=F(0)` and `L=DF(0)`.
Every coordinate of `f` is diagonal and every coordinate of `LH` has
zero diagonal. With the real HS inner product,

```text
<f,LH> = Re sum_j tr_n(f_j^*(LH)_j)=0
```

for every admissible anti-Hermitian tuple `H`. Hence

```text
L*f=0,          LL*f=0.                              (5)
```

In particular the derivative of `||F||_2^2/2` vanishes. For every
positive threshold `sigma`, if `e>0` then

```text
||1_([0,sigma^2))(LL*)f||_2=e,                        (6)
```

rather than the `e/8` required by the conditional contraction theorem.
Every proposed update `L*p(LL*)f` is zero, since `p(LL*)f=p(0)f`.
This includes every finite Landweber update, independently of its
degree. The assertion concerns these specified first-order updates;
it does not exclude leaving the stationary point by surgery, another
direction, or a second-order method. Stationarity does not imply a
local minimum.

## 3. Balanced stationary points approach their compatible stratum

Let `omega=exp(2pi i/3)`. On twelve coordinates put

```text
S=diag(1,1,1,1,1,1,-1,-1,-1,-1,-1,-1),
B=diag(1,1,1,1,omega,omega,omega,omega,
       omega^2,omega^2,omega^2,omega^2).
```

Use this same commuting representation at both vertices, and adjoin
`n-12` trivial coordinates for every `n>=12`. Both central involutions
are positive. With `t=s^(-1)b`, the edge map sends `t` to `t^2` and
`l_2=(s b^(-1))^2` to `l_1=s b^(-1)`. Therefore the two noncentral
residuals on the displayed block are

```text
R_t=SB-B^2,       R_l=B-SB^2;                         (7)
```

the central residual is zero. The two residual moduli agree coordinate
by coordinate. Their squared values are zero on the first four
coordinates, three on the next two, and one on the final six. Thus

```text
||R_t||_F^2=||R_l||_F^2=12,
e^2=24/n,          rank(P)=8.                        (8)
```

These nonzero residuals satisfy (5), so the entire sequence is stationary.
The maximum generator-normalized-HS convention for defect would give
`def=sqrt(12/n)`; (8) uses the Hilbert tuple convention of the polynomial
step. Its operator residual is `sqrt(3)`, and does not tend to zero.

There is a compatible comparison in exactly the same multiplicity
stratum. Reduce `SL_2(Z[1/2])` modulo three and take the twelve-dimensional
regular representation of `PSL_2(F_3)=A_4`, then adjoin `n-12` trivial
coordinates. At either modular vertex, the images of `s,b` have orders
two and three. In a regular representation, left translation by an
element of order `m` has each `m`th-root eigenvalue with multiplicity
`12/m`. Thus all four generator multiplicity lists agree with the input.
Call this compatible pair `eta_n`. It differs only on twelve coordinates,
so

```text
max_U ||q_n(U)-eta_n(U)||_2 <= 2sqrt(12/n).            (9)
```

Equality of the multiplicities also gives a path inside the product
of torsion strata: choose a unitary conjugator for each corresponding
generator on the twelve-dimensional block. Each has an anti-Hermitian
logarithm of operator norm at most `pi`. Conjugation by its exponential
path preserves the positive central relation. With maximum generator
HS speed the product path has length at most `2pi sqrt(12/n)`.
Thus even intrinsic stratum distance tends to zero.

These examples are explicitly repairable by (2), at rank eight and
HS cost at most `2sqrt(8/n)`. They do not provide a strict-instability
counterexample. They prove that a compatible stratum and small HS
distance do not supply the residual spectral hypothesis. On this
subclass the exact support surgery supplies the missing action instead.

## 4. What this leaves open

The construction solves capture only when all four input generators
commute jointly. A general residual support can fail to reduce the
vertices, and replacing generators on it can break the modular relations.
The previously proved cyclic-hull surgery retains those relations but
can create new residual outside the selected support. No contraction
for that general operation follows from (1)--(3). Obtaining controlled
residual capture for genuinely noncommuting inputs remains the step
needed by the flexible repair route.
