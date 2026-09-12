# Natural-module atlas deformations fail to all orders over every field

Date: 2026-08-12

## Theorem

Let (k) be any field, let (V=k^8) be the natural permutation module of
(A_8), and use the fixed classical inner alignment of the two full atlas
charts. For (Nge2), put

\[
 D_N=k[\varepsilon]/(\varepsilon^N)
\]

and let

\[
 A(\varepsilon)=I+\varepsilon X_1+\cdots+
 \varepsilon^{N-1}X_{N-1}\in GL(V\otimes_kD_N).
\]

Conjugate only the second chart by (A(\varepsilon)). Assume the 24
certified-zero words remain trivial and the four survivor words

\[
 s_{11},s_{30},s_{44},s_{55}
\]

commute with the full first (A_8)-chart. Then

\[
 \rho_A(s_{11})=I.                                  \tag{NH1}
\]

Thus merely changing the coefficient field or increasing the univariate
nilpotent order cannot rescue the natural eight-point atlas construction.

## Odd characteristic

Linearizing the 24 zero constraints and the commutant-valued centrality of
the four survivors gives an integral matrix

\[
 C:\operatorname{End}_{\mathbb Z}(\mathbb Z^8)
   \longrightarrow\mathbb Z^{3072}.                 \tag{NH2}
\]

An exact rational audit gives (operatorname{rank}_{mathbb Q}C=62). More
strongly, the archived row and column indices select a (62\times62) minor
with

\[
 |\det C_0|=8192=2^{13}.                             \tag{NH3}
\]

Therefore (C) has rank 62 over every field of odd characteristic. The
two-dimensional permutation-module commutant

\[
 \operatorname{End}_{A_8}(V)=\langle I,J\rangle_k   \tag{NH4}
\]

always lies in (ker C), so `(NH3)` proves equality for every odd field.

Now take the first coefficient (X_m) of (A(\varepsilon)) which is not in
the commutant. Right multiplication of (A) by an invertible
commutant-valued series does not change the conjugated chart and removes all
earlier commutant coefficients. At order (\varepsilon^m), the nonlinear
equations reduce exactly to the homogeneous system (C(X_m)=0), contradicting
`(NH3)`--`(NH4)`. Hence the whole series is gauge-equivalent to a
commutant-valued series, which does not change the second chart at all; this
proves `(NH1)` in odd characteristic.

## Characteristic two

Modulo two, the same system has rank 61 and a one-dimensional
noncommutant quotient of its kernel. Let (X_*) denote its nonzero quotient
class. The exact truncated-ring calculation proves that the quadratic
right-hand side produced by (X_*) does not belong to the image of (C); the
archived representative has matrix weight 20. Equivalently, no choice of a
second coefficient extends (I+\varepsilon X_*) through order
(\varepsilon^2). This is the quadratic obstruction already underlying
`FALSE_ATLAS_BOOLEAN_DUAL_NO_GO.md`.

The same first-noncommutant-coefficient argument applies over every field
of characteristic two. After removing the preceding commutant-valued
series, a further commutant gauge in degree (m) lets us write the first
noncommutant coefficient as (X_m=aX_*) with (a\ne0), modulo the fixed
choice of representative (X_*). If (2m<N), the equations in
degree (2m) have quadratic right-hand side (a^2) times the certified
right-hand side for (X_*). Since scalar extension preserves membership in
the image of (C), and (a^2\ne0), no coefficient (X_{2m}) can solve those
equations. If (2m\ge N), products of noncommutant coefficients are invisible
modulo (\varepsilon^N). Every visible coefficient of the marked survivor is
then a first-order expression in one coefficient of (A), with lower
commutant coefficients contributing nothing. The all-module first-order
identity forces each such coefficient to vanish. Thus `(NH1)` holds in
characteristic two as well.

The determinant witness, the one-dimensional quotient, and the affine
inconsistency are preserved under scalar extension from the prime field.
This completes the all-fields statement.

## Exact replay

The verifier constructs the integral derivative matrix directly from atlas
prefixes, checks its convention against truncated-matrix word evaluation,
computes the determinant witness, and independently replays the quadratic
systems in characteristics (2,3,17):

```text
module load sagemath/10.7
PYTHONPATH=experiments sage -python \
  experiments/atlas_natural_all_field_higher_order.py \
  --primes 2,3,17 --max-tangents 20 --exact-rank-audit \
  > experiments/atlas-natural-all-field-higher-order.json
```

Archived output SHA-256:

```text
eeba09db179087df0f7019b01faf212aebb6f03f01964e38e12d16e812bb8518
  experiments/atlas-natural-all-field-higher-order.json
```

## Scope

This theorem is universal in the coefficient field and nilpotent order, but
specific to:

1. the natural eight-point permutation module;
2. one common module for both charts;
3. the fixed inner order-zero alignment; and
4. a univariate truncated-power-series deformation.

It does not prove analytic unitary local rigidity, exclude singular branches
with no formal expansion around the classical fold, classify other order-zero
holonomies, or prove the Leavitt witness nonhyperlinear. Together with the
all-module square-zero theorem, it says that a surviving FALSE atlas must
combine genuinely nonlinear geometry with a non-natural representation,
different chart modules, or different order-zero holonomy.
