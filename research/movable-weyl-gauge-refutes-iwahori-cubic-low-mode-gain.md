---
rg: 2
id: movable-weyl-gauge-refutes-iwahori-cubic-low-mode-gain
kind: claim
title: A movable exact Weyl gauge saturates the quadratic low-mode bound despite both cubics
distinct_from:
  bs14-periodic-koopman-modes-refute-skeleton-regularity: that realizes the slow mode in the exact BS skeleton but not as a residual of a full approximate Iwahori tuple; this realizes it as the projected Weyl residual of such a tuple while bounding every full-presentation relator.
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that asks for the sharp weighted sum over all bands; this disproves only the stronger positive-exponent estimate on each individual band.
---

**ESTABLISHED COUNTERPACKET.**  There is no universal
`epsilon>0,C<infinity` for which every full approximate Iwahori tuple obeys

```text
||P_t(e'-1)||_2^2 <= C delta^2 t^(2+epsilon).           (MWG1)
```

The same conclusion applies if `P_t e'` silently centers the near-identity
residual, as in the original claim.

## Exact finite packets

For `L>=3` put `N=4^L-1`.  Reduction modulo `N` gives an exact finite
quotient representation of the square-root presentation

```text
<x,r,s | x^2, (xr)^2, (xs^2)^3,
         rsr^(-1)s^(-4), (xrs)^3>.                     (MWG2)
```

Use its regular representation.  The upper parabolic `V=pi(s)` has order
`N`, and `h=pi(r)` acts on its spectral characters by fourth power.  The
character of exponent one has orbit of exactly length `L`: `4^L=1 mod N`,
whereas `4^k-1<N` for `0<k<L`.

Let `p_0,...,p_(L-1)` be the equal-rank spectral projections on that orbit,
let

```text
q=sum_j p_j,       mu=tau(q)=L/N,
z=sum_j exp(2 pi i j/L) p_j,
a=(z+z^*)/2.                                           (MWG3)
```

Then `a=a^*`, `||a||_infinity<=1`, and `a` belongs to the base commutant
`Z={V}'`.  For `psi=Ad(h)` its two nonzero Fourier components are the first
positive and negative modes.  With `g_L=|1-exp(2 pi i/L)|`,

```text
b=a-psi(a),       ||b||_2^2=mu g_L^2/2.                (MWG4)
```

In particular `b` is orthogonal to the fixed algebra.

## Reverse one exact correction

Put `c_alpha=exp(i alpha a)`.  Keep the exact BS core and all other
generators fixed, but replace the exact Weyl swap by the swap before its
correction by `c_alpha`.  The correction convention computed in
`solenoid-absorption-cascade-converges` is

```text
c psi(c)^(-1)=e'.                                      (MWG5)
```

Consequently this perturbed full tuple has projected residual

```text
e'_alpha=c_alpha psi(c_alpha)^(-1)=exp(i alpha b).      (MWG6)
```

Here `(MWG6)` uses that `a` and `psi(a)` lie in the same abelian spectral
algebra.  Reversing the left/right correction convention only inverts this
unitary or reverses the cyclic orientation, neither of which changes the
band norm below.  Thus the conditional expectation onto `Z` changes nothing, and
removing the fixed algebra changes neither first Fourier component.

Let `t_L` be the least dyadic number at least `g_L`; then
`g_L<=t_L<2g_L`, and `t_L` lies in `(0,1]` for large `L`.  Both first modes
lie in the band `t_L/2<|1-psi|<=t_L`.  Differentiability of the exponential in
finite-dimensional `L^2` gives, for each `L` and all sufficiently small
positive `alpha`,

```text
||P_(t_L)(e'_alpha-1)||_2^2
 >= alpha^2 ||b||_2^2/4
 =  alpha^2 mu g_L^2/8.                                (MWG7)
```

On the other hand the presentation is fixed.  If `m` is the maximum number
of occurrences of the Weyl generator in one relator, word telescoping gives

```text
delta_alpha
 <= m ||c_alpha-1||_2
 <= m alpha ||a||_2
 <= m alpha sqrt(mu/2).                                (MWG8)
```

This bounds all five rows of `(MWG2)`, in particular both cubic rows; no
claim that either cubic is exact is used.

If `(MWG1)` held, `(MWG7)--(MWG8)` would imply

```text
alpha^2 mu g_L^2/8
 <= C m^2 alpha^2 mu t_L^(2+epsilon)/2.
```

Canceling the positive common factors leaves a fixed constant bounded by a
constant times `g_L^epsilon`, impossible because `g_L -> 0`.

## Sharp interpretation

The correction itself has `||c_alpha-1||_2=O(alpha sqrt(mu))`, hence is
`O(delta_alpha)`, and its weighted inverse contribution is

```text
||P_(t_L)(e'_alpha-1)||_2^2/t_L^2=O(delta_alpha^2).
```

This family is harmless for repair: it is a movable exact gauge whose
amplitude is paid by the cubic defects.  It refutes the extra pointwise
exponent, not the aggregate weighted estimate.  A corrected claim must
either sum the `t^(-2)` energy directly against the full relator budget or
first minimize over `O(delta)` base-commutant corrections.
