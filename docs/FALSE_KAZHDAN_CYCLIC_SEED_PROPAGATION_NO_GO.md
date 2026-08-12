# Property (T) propagates one cyclic seed without word-length loss

Date: 2026-08-12

## 1. Outcome

The inverse-root word length isolated in
`FALSE_FROBENIUS_CYCLIC_VECTOR_MIXING_NO_GO.md` is **not** an escape when
the two base actions and their tangent covariance are exact. Property
`(T)` replaces the earlier telescoping factor by a dimension-free Kazhdan
constant.

Let `Gamma=<S>` have property `(T)`, with spectral-gap constant `kappa>0`
in the form

\[
 \operatorname {dist}(\xi,\operatorname {Fix}_\Gamma \beta)
 \leq \kappa^{-1}\max_{s\in S}\|\beta(s)\xi-\xi\|
 \tag{KSP1}
\]

for every finite-dimensional unitary representation `beta`. Let `W` be a
`Gamma`-module, and let two exact covariant unitary realizations be given by

\[
 \rho_i:\Gamma\longrightarrow U(d),\qquad
 \Phi_i:W\longrightarrow U(d),\qquad i=0,1,
 \tag{KSP2}
\]

where `W` is written additively, each `Phi_i` is a group homomorphism, and

\[
 \rho_i(g)\Phi_i(w)\rho_i(g)^*=\Phi_i(gw).
 \tag{KSP3}
\]

For `z,w in W`, define the orbit coefficient norm

\[
 c_\Gamma(w;z)=
 \min\left\{\sum_{\nu=1}^m|n_\nu|:
 w=\sum_{\nu=1}^m n_\nu g_\nu z\right\},
 \tag{KSP4}
\]

with value `infinity` if `w` is not in the integral orbit span of `z`.

The main estimate is

\[
 \boxed{
 \|\Phi_0(w)T-T\Phi_1(w)\|_2
 \leq C\epsilon+\frac{2(C+1)}{\kappa}\eta,
 }
 \tag{KSP5}
\]

where `T in U(d)`, `C=c_Gamma(w;z)`, and

\[
 \epsilon=\|\Phi_0(z)T-T\Phi_1(z)\|_2,
 \qquad
 \eta=\max_{s\in S}\|\rho_0(s)T-T\rho_1(s)\|_2.
 \tag{KSP6}
\]

There is no word length of the elements `g_nu` in `(KSP5)`.

For the finite Frobenius tangent module, the explicit four-orbit identity
proves

\[
 c_H(z_-;z_+)\leq 2r.
 \tag{KSP7}
\]

Consequently

\[
 \|\Phi_0(z_-)T-T\Phi_1(z_-)\|_2
 \leq 2r\epsilon+\frac{4r+2}{\kappa}\eta.
 \tag{KSP8}
\]

Thus `epsilon_n,eta_n->0` forces the marked fold to disappear even if the
positive word length of `x_1^(-1)` tends to infinity arbitrarily fast. A
successful paired Fourier/Frobenius construction must make the base action
or the tangent covariance itself genuinely nonliftable; concentrating a
small intertwining defect along a long inverse-root word is insufficient.

## 2. The bimodule projection

Give `M_d(C)` the normalized Hilbert--Schmidt norm and define

\[
 \beta(g)X=\rho_0(g)X\rho_1(g)^*.
 \tag{KSP9}
\]

This is a unitary representation of `Gamma`. Let `P` be the orthogonal
projection onto its invariant space and put

\[
 X=PT,\qquad \delta=\|T-X\|_2.
 \tag{KSP10}
\]

The invariant space is precisely the exact intertwiner space:

\[
 \rho_0(g)X=X\rho_1(g),\qquad g\in\Gamma.
 \tag{KSP11}
\]

Moreover `(KSP1)` and unitary invariance give

\[
 \delta
 \leq\kappa^{-1}\max_{s\in S}
       \|\rho_0(s)T\rho_1(s)^*-T\|_2
 =\frac{\eta}{\kappa}.
 \tag{KSP12}
\]

Although `X` need not be unitary, this causes no problem. The proof only
uses it as an exact base intertwiner.

The seed discrepancy for `X` satisfies

\[
 \begin{aligned}
 \|\Phi_0(z)X-X\Phi_1(z)\|_2
 &\leq \|\Phi_0(z)T-T\Phi_1(z)\|_2+2\|T-X\|_2\\
 &\leq\epsilon+2\delta.
 \end{aligned}
 \tag{KSP13}
\]

## 3. Exact covariance removes all transport length

Fix `g in Gamma`. Combining `(KSP3)` and `(KSP11)` gives the exact
identity

\[
 \begin{aligned}
 &\Phi_0(gz)X-X\Phi_1(gz)\\
 &\quad=\rho_0(g)
       \bigl(\Phi_0(z)X-X\Phi_1(z)\bigr)
       \rho_1(g)^*.
 \end{aligned}
 \tag{KSP14}
\]

Therefore

\[
 \|\Phi_0(gz)X-X\Phi_1(gz)\|_2
 \leq\epsilon+2\delta
 \tag{KSP15}
\]

for **every** `g`, with no dependence on `ell_S(g)`.

For unitaries `U,V` and an arbitrary matrix `X`, telescoping gives

\[
 \|U^nX-XV^n\|_2\leq |n|\|UX-XV\|_2,
 \qquad n\in\mathbb Z.
 \tag{KSP16}
\]

Likewise, for finite unitary lists,

\[
 \left\|\prod_{j=1}^mU_jX-X\prod_{j=1}^mV_j\right\|_2
 \leq\sum_{j=1}^m\|U_jX-XV_j\|_2.
 \tag{KSP17}
\]

If

\[
 w=\sum_{\nu=1}^m n_\nu g_\nu z,
 \tag{KSP18}
\]

then additivity of `Phi_i`, followed by `(KSP15)--(KSP17)`, yields

\[
 \|\Phi_0(w)X-X\Phi_1(w)\|_2
 \leq\left(\sum_\nu|n_\nu|\right)(\epsilon+2\delta).
 \tag{KSP19}
\]

Returning from `X` to `T` costs at most `2delta`. Taking a coefficient
minimizer in `(KSP4)` gives

\[
 \|\Phi_0(w)T-T\Phi_1(w)\|_2
 \leq C\epsilon+2(C+1)\delta.
 \tag{KSP20}
\]

Substitution of `(KSP12)` proves `(KSP5)`.

## 4. Frobenius specialization

Use the notation of
`FALSE_FROBENIUS_CYCLIC_VECTOR_MIXING_NO_GO.md`:

\[
 H=E_r(B),\qquad
 z_+=P x_2\otimes a,\qquad
 z_-=P x^{e_2-e_1}\otimes a,
 \tag{KSP21}
\]

where `r>=4` is even and `2` is invertible in the finite coefficient ring.
The explicit four-orbit formula there writes every opposite-parity diagonal
difference with four signed translates of `z_+`; summing over the `r/2`
opposite-parity pairs writes `z_-` with `2r` signed translates. This is
exactly `(KSP7)`.

If the finite groups `H_n` are quotients of one fixed Kazhdan group
`Gamma`, the quotient representations inherit the same constant `kappa`
for the image of the fixed Kazhdan set. Apply `(KSP5)` with `C<=2r` to get
`(KSP8)`, uniformly in the ring size, module dimension, clock order, and
positive word length of the inverse root.

This corrects the apparent escape `(FCM8)` in the earlier note. That escape
exists for arbitrary approximately covariant systems, but not when the
base matrices are exact representations of a fixed property-`(T)` group
and `(KSP3)` is exact. In that exact-base regime, averaging in the
Hilbert--Schmidt bimodule reaches a true base intertwiner before any long
word is traversed.

## 5. Consequence for the FALSE program

The following completion is impossible:

1. choose two exact finite base representations of the Kazhdan vertex;
2. realize the finite tangent modules with exact covariance;
3. choose a wall which approximately intertwines the base generators and
   exactly or approximately aligns the common positive cyclic seed; and
4. use the growing positive length of `x_1^(-1)` to retain the fold.

Equations `(KSP5)--(KSP8)` show that Step 4 cannot occur. The inverse-root
distortion proved in `FALSE_POSITIVE_INVERSE_ROOT_LINEAR_DISTORTION.md` is
real algebraically, but it cannot amplify a defect after Kazhdan projection
in an exact covariant representation.

The live endpoint is narrower:

> at least one vertex/base map must be a genuinely nonliftable normalized-
> Hilbert--Schmidt almost-representation, or the tangent covariance itself
> must fail by an amount not controlled by the same vanishing defect.

This agrees with `FINITE_REPRESENTATION_MATCHING_BARRIER.md`, which proves
the analogous statement directly for two exact vertex representations.
The present theorem acts one layer earlier: one cyclic tangent seed and
exact covariance already propagate through the entire Frobenius module,
without paying the inverse-root word length.
