# Property `(T)` forces linear primitive-holonomy moments

Date: 2026-08-11

## 1. Outcome

The property-`(T)` estimate in
`FALSE_PRINCIPAL_BUNDLE_CONSTANT_COEFFICIENT_NO_GO.md` has a stronger
consequence than positive density of nonzero fiber holonomy.  For a primitive
order-`M` clock coordinate, some fixed Kazhdan generator has mean centered
exponent proportional to `M`:

\[
\max_{s\in S}\frac1{|X|}\sum_{x\in X}|d_s(x)|_M
\geq \frac{\kappa^2}{4\pi}M.                         \tag{PHM1}
\]

Here `|.|_M` is the centered absolute representative in `[0,M/2]`, and
`kappa` is a Kazhdan constant for the fixed generating set `S`.
Consequently the corresponding RMS moment is also linear in `M`.

This closes the scalar induced-Weyl-seam splice for the exact
principal-bundle clock.  The corrected seam criterion requires each forced
transition coordinate to be sublinear separately, in addition to the
product condition.  A primitive bundle holonomy violates that endpoint
condition uniformly, no matter how small the other Weyl coordinate becomes.

The theorem does **not** rule out the paired Fourier/Frobenius route.  That
route changes the tangent representation with the base point instead of
encoding the principal holonomy as one scalar Weyl translation coordinate.

## 2. Abstract primitive-clock theorem

Let `Gamma` have property `(T)`, let `S` be a finite symmetric generating
set with Kazhdan constant `kappa>0`, and fix `t in Gamma`.  Let `X` be a
finite `Gamma`-set.  Suppose every `t`-orbit has length divisible by `M` and
there is a function

\[
r:X\longrightarrow \mathbb Z/M\mathbb Z
\]

such that

\[
r(tx)=r(x)+1.                                         \tag{PHM2}
\]

Put `omega=exp(2 pi i/M)` and

\[
z(x)=\omega^{r(x)}.                                   \tag{PHM3}
\]

For `s in S`, define

\[
d_s(x)=r(s^{-1}x)-r(x)\pmod M                        \tag{PHM4}
\]

and take its centered representative.

**Theorem 1 (linear holonomy moment).**  In the normalized counting norm,

\[
\max_{s\in S}
\mathbb E_x\left|\omega^{d_s(x)}-1\right|^2
\geq\kappa^2,                                        \tag{PHM5}
\]

and hence `(PHM1)` holds.  If

\[
A_s=\mathbb E_x|d_s(x)|_M,
\qquad
R_s^2=\mathbb E_x|d_s(x)|_M^2,                       \tag{PHM6}
\]

then

\[
\max_s A_s\geq\frac{\kappa^2}{4\pi}M,
\qquad
\max_s R_s\geq\frac{\kappa^2}{4\pi}M.              \tag{PHM7}
\]

### Proof

Equation `(PHM2)` makes `z` run through all `M`-th roots of unity equally
often on every `t`-orbit.  Its average on every `t`-orbit is zero.  Every
`Gamma`-orbit is a union of `t`-orbits, so `z` is orthogonal to all invariant
vectors in `ell^2(X)` and has normalized norm one.

Property `(T)` therefore gives an `s in S` with

\[
\|sz-z\|_2^2\geq\kappa^2.                            \tag{PHM8}
\]

By `(PHM3)--(PHM4)`, the left side is the average in `(PHM5)`.

For a centered integer `a`, put `u=pi|a|/M`, so `0<=u<=pi/2`.  The elementary
inequality

\[
\sin^2 u\leq u                                       \tag{PHM9}
\]

follows because the derivative of `u-sin^2 u` is `1-sin(2u)>=0`.  Hence

\[
|\omega^a-1|^2
=4\sin^2(\pi|a|/M)
\leq4\pi |a|/M.                                      \tag{PHM10}
\]

Averaging `(PHM10)` for the generator supplied by `(PHM5)` gives the first
inequality in `(PHM7)`.  The normalized counting inequality
`R_s>=A_s` gives the second.  End proof.

The same proof works after multiplying `r` by any unit modulo `M`: the
resulting clock is still primitive and still has mean zero on each
`t`-orbit.  Thus unit normalization of the clock character cannot evade the
linear-moment conclusion.

## 3. Consequence for the induced Weyl seam

The scalar seam bound has the form

\[
C_1R^2L^2/M^2+C_2A/L,
\qquad 1\leq L\leq M.                                \tag{PHM11}
\]

`FALSE_INDUCED_WEYL_SEAM_ENDPOINT_AUDIT.md` proves that a sequence of seam
widths can make `(PHM11)` vanish if and only if

\[
R=o(M),\qquad A=o(M),\qquad RA=o(M).                 \tag{PHM12}
\]

In the exact principal-bundle construction, the prescribed primitive clock
holonomy gives a coordinate `d_s(x)` of the transition system.  If it is the
first Weyl coordinate, `(PHM7)` violates `R=o(M)`; if it is the second, it
violates `A=o(M)`.  This remains true after a change of transversal or a unit
renormalization because Theorem 1 applies to every function satisfying
`(PHM2)`.

Therefore:

**Corollary 2 (primitive principal-bundle seam no-go).**  No scalar
block-diagonal Weyl seam carrying the prescribed primitive principal-bundle
clock coordinate can satisfy the simultaneous fixed-generator criterion
`(PHM12)`.

This explains why the old product-only test was misleading.  If the other
moment happened to vanish, `RA/M` would also vanish, while the surviving
linear coordinate would still leave a constant endpoint cost.  The two
separate sublinearity conditions detect exactly this failure.

## 4. Consequence for the coherent-lift shortcut

`FALSE_IOANA_COHERENT_SCHREIER_LIFT_CRITERION.md` gives a strong conditional
route to bounded transition moments: coherently lift all finite cocycles to
one countable `BS(1,p+1)`-valued cocycle, apply profinite cocycle rigidity,
and gauge the resulting finite-stage values into the integral horocyclic
chart.

For the primitive principal bundle, Theorem 1 shows that the last conclusion
cannot hold.  If a coordinate of the reduced transition cocycle is the
primitive difference `(PHM4)`, then some fixed generator has centered
coordinate at least `kappa^2 M/(4 pi)` in mean.  It therefore cannot be the
reduction of a uniformly bounded finite list of integral coordinates after
gauge.

Thus, whenever the coherent lift is required to reproduce `(PHM2)`, at least
one of the following must fail:

1. the growing transition systems are reductions of one fixed countable
   cocycle;
2. the rigidity transfer is compatible with the prescribed finite
   principal-bundle coordinate; or
3. the finite-stage representative is gaugeable into the integral
   horocyclic chart.

This does not contradict the conditional theorem in the Ioana note.  It
proves that its integral-chart conclusion is unavailable for the exact
primitive scalar bundle which motivated the seam.

## 5. Remaining live globalization

The conclusion applies to a scalar transition-coordinate repair on the
principal bundle.  It does not apply to a base-dependent representation in
which the forced holonomy is absorbed by changing the tangent embedding or
Fourier polarization itself.  The surviving FALSE target is therefore the
finite equivariant Frobenius-module problem from
`FALSE_LONG_FROBENIUS_ELEMENTARY_COMPRESSOR.md`, subject to the monodromy
obstruction in `FALSE_LONG_CHAIN_BUNDLE_MONODROMY_NO_GO.md`.

Future computation should not optimize the scalar moments in `(PHM12)` for
the primitive principal bundle: Theorem 1 gives a dimension-free lower bound.
It should search only genuinely nonconstant tangent functors or
higher-incidence holonomy-canceling constructions.
