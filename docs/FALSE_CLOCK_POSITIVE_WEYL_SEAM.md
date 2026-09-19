# The absorbed finite clock has an explicit vanishing-cost Weyl seam

Date: 2026-08-11

## 1. Outcome

The restriction of the finite split-clock multiplier to the natural
translation-positive subgroup is not only asymptotically repairable in
normalized Hilbert--Schmidt norm; it has an explicit sparse-seam repair with
a quantitative rate.

Fix an odd prime `p`, put

\[
M=p^k,
\qquad n=p^{k+1},
\qquad q=1+p,
\]

and let

\[
P_k=J_k\times\langle h\rangle,
\qquad |h|=n,
\]

where `J_k=Aug_(Z/n)(C_M)`.  Restrict the explicit multiplier from
`FALSE_SPLIT_CLOCK_EXPLICIT_COCYCLE.md` to `P_k`.  After normalizing a
primitive central character by one unit power, this restriction is the
inflation of the standard two-dimensional Weyl multiplier on `(Z/M)^2`.

Consequently there are diagonal gauges `W_k` such that the twisted and
ordinary left regular representations agree asymptotically on every fixed
bounded Weyl window.  With a seam width `L|M`, the two basic squared errors
are bounded by

\[
4\pi^2L^2/M^2
\qquad\hbox{and}\qquad
4/L.
\]

Taking `L=p^ell` with `ell` nearest `2k/3` makes both errors
`O(M^(-2/3))`, hence both normalized HS errors are `O(M^(-1/3))`.

At the same time, the `p^(k-1)`-fold central commutator has the fixed phase

\[
\exp(2\pi i/p).
\]

Thus exact positive-side absorption of the growing Schur class does **not**
produce a local metric obstruction.  The local positive clock sector already
has exactly the micro--macro profile required by phase splitting.  The
remaining obstruction is its equivariant globalization over the other
positive and external generators.

## 2. Restriction of the mixed cocycle

Use additive notation for `J_k`.  The crossed homomorphism defining the
clock class satisfies

\[
\alpha_k(h)=\lambda_k,
\qquad
\alpha_k(c)=0,
\]

and `h` acts trivially on `J_k`.  Therefore on

\[
g=(x,h^a),
\qquad t=(y,h^b)
\]

the additive cocycle is

\[
\omega_k(g,t)=a\lambda_k(y)\pmod n.                 \tag{WSC1}
\]

Every value of `lambda_k` is divisible by `p`.  Hence

\[
r_0(y)=\lambda_k(y)/p\pmod M                         \tag{WSC2}
\]

is a homomorphism `J_k -> Z/M`.  For the distinguished augmentation vector

\[
v=e_0-e_1,
\]

the value `u=r_0(v)` is a unit modulo `p`, hence a unit modulo `M`.  Let
`b=u^(-1) mod M`, replace `r_0` by

\[
r=br_0,                                              \tag{WSC3}
\]

and replace the primitive central character `chi(z)=exp(2 pi i z/n)` by
the equally primitive character `chi^b`.  (Here `b` may be lifted to a unit
modulo `n`; in the displayed orientation one can take `b=q`.)  Then
`r(v)=1`, and equation `(WSC1)` becomes

\[
\exp\left(\frac{2\pi i}{M}a r(y)\right).            \tag{WSC4}
\]

Define the quotient homomorphism

\[
\pi_k:P_k\longrightarrow A_M=(\mathbb Z/M)^2,
\qquad
\pi_k(x,h^a)=(r(x),a\bmod M).                        \tag{WSC5}
\]

If `zeta=exp(2 pi i/M)`, the multiplier `(WSC4)` is the inflation along
`pi_k` of

\[
\Omega((s,t),(s',t'))=\zeta^{t s'}.                 \tag{WSC6}
\]

This is the standard Weyl multiplier.

The character normalization is essential.  The standard representative of
the modular inverse `q^(-1) mod M` need not stay bounded as `k` grows, so it
is invalid to infer a small real phase directly from that representative.
Multiplying the character by the inverse unit before passing to the circle
makes the distinguished coordinate *exactly* `1 mod M`; all subsequent
small-phase estimates are then invariant statements rather than choices of
integer representative.

## 3. Sparse seam gauge

Let `e_1=(1,0)` and `e_2=(0,1)` in `A_M`.  Choose a divisor `L|M` and, for
`0<=s,t<M`, put

\[
f(t)=t\bmod L\in\{0,\ldots ,L-1\},
\qquad
a(s,t)=\zeta^{-s f(t)}.                              \tag{WSC7}
\]

On `ell^2(P_k)`, let `W_k` be the diagonal unitary

\[
W_k\delta_g=a(\pi_k(g))\delta_g.                    \tag{WSC8}
\]

Write `lambda_Omega` for the twisted left regular representation determined
by `(WSC4)` and `lambda` for the ordinary left regular representation.  The
two matrices have the same underlying permutation.  Their entrywise phase
ratio after `(WSC8)` depends only on `pi_k(g)`.  Every fiber of `pi_k` has
the same size, so its normalized squared HS norm is exactly the corresponding
average over `A_M`.

The elementary seam calculation gives

\[
\|W_k\lambda_\Omega(e_1)W_k^*-\lambda(e_1)\|_2^2
\leq 4\pi^2L^2/M^2,                                 \tag{WSC9}
\]

\[
\|W_k\lambda_\Omega(e_2)W_k^*-\lambda(e_2)\|_2^2
\leq 4/L.                                            \tag{WSC10}
\]

For completeness, `(WSC9)` comes from the smooth phase variation
`zeta^(f(t))`, whose angle is at most `2 pi L/M`.  In `(WSC10)`, the gauge
cancels the Weyl phase except when `t -> t+1` crosses one of the `M/L`
seams.  The exceptional fraction is `1/L`, and every squared chord is at
most four.

Choose `ell=floor(2k/3)` or `ceil(2k/3)` and `L=p^ell`.  Then

\[
L\longrightarrow\infty,
\qquad
L/M\longrightarrow0,                                \tag{WSC11}
\]

and both errors tend to zero.  By the unitary telescoping inequality, the
same holds for every fixed word in `e_1,e_2`.  More generally, it holds for
any family of labels whose coordinates in this basis stay bounded as `k`
grows.

Fixed translates of the distinguished augmentation vector have this
property.  Indeed `lambda_k(c^jv)/lambda_k(v)` is a fixed power of `q` for
fixed `j`, so after the normalization `(WSC3)` its Weyl coordinate is bounded
independently of `k`.

## 4. The marked phase survives the seam

Let `X_k,Z_k` denote the two projective Weyl generators.  Their commutator is

\[
[Z_k,X_k]=\zeta I.                                   \tag{WSC12}
\]

The order-`p` Bockstein shadow of the order-`p^k` clock direction is the
`p^(k-1)` multiple.  Therefore

\[
[Z_k,X_k]^{p^{k-1}}
=\exp(2\pi i/p)I.                                    \tag{WSC13}
\]

Its normalized HS distance from the identity is the fixed positive number

\[
|\exp(2\pi i/p)-1|.                                  \tag{WSC14}
\]

The diagonal gauge does not alter a scalar commutator holonomy.  Equations
`(WSC9)--(WSC14)` therefore exhibit an explicit sequence in which all fixed
local Weyl labels are repairable at vanishing normalized HS cost but the
growing Bockstein collision remains macroscopic.

## 5. Consequence for the main FALSE route

This theorem closes the local metric question left open by the exact
restriction computation:

* the map from the positive subgroup absorbs the growing clock class in
  exact `H_2`;
* nevertheless its central-character matrices are asymptotically equivalent
  to the untwisted positive model on every fixed bounded clock window; and
* the marked Bockstein phase remains visible.

There is no need to search numerically for a gauge on this local subgroup;
`(WSC7)` is an explicit one with a proved rate.

What remains is a simultaneous equivariant seam theorem.  After Shapiro
induction into the finite vertex, the other fixed generators create a finite
family of twisted transition coordinates.  One must extend `(WSC7)` so their
normalized energy also tends to zero, or prove that the paired Fourier
finite-module construction realizes the same seam functorially.  The
external and base covariance cannot be discarded: exact tautological
principal-bundle absorption is known to kill the fold.

Thus the next computation should target only the new transition coordinates
outside the local `(h,v)` Weyl plane.  Recomputing local Schur multipliers or
optimizing the two-dimensional seam would duplicate solved work.
