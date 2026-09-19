# The hard-pair Leavitt star cannot be read as operator adjoint

Date: 2026-08-13

## Exact outcome

The four-term characteristic-two certificate

\[
 p_{001}=
 l^\star l+(q^\star)^2l^\star l+l^\star lq^2+
 (q^\star)^2l^\star lq^2
 \tag{HSI1}
\]

does not directly define a projection in a complex unitary microstate.  The
symbol `star` in `(HSI1)` is the Leavitt ring anti-involution.  It is not
group inversion on the hard-prefix units.

For the first class-11 hard pair, exact all-depth Leavitt arithmetic gives

\[
 |q|=4,
 \qquad |l|=2,
 \qquad q^\star\ne q^{-1},
 \qquad l^\star\ne l^{-1}.
 \tag{HSI2}
\]

The distinction is load-bearing.  If one replaces every Leavitt star in
`(HSI1)` by group inverse, as a unitary representation would require for an
operator adjoint, the right side becomes

\[
 1+q^{-2}+q^2+q^{-2}q^2
 =q^{-2}+q^2=0,
 \tag{HSI3}
\]

because `q^4=1`.  The correct Leavitt-star expression equals the nonzero
cylinder projection `p_001`, while the inverse-substituted expression
vanishes exactly.

Thus the tempting simplification of the projection-recovery gate through a
single hard-word spectral polynomial is false.  It does not merely worsen a
constant: it maps the desired carrier to zero.

## Consequence for the live route

The hard certificate can still be transported through the elementary root
law.  For a fixed root, characteristic-two addition is group multiplication,
and multiplication of coefficients is encoded by cross-root Steinberg
commutators.  Fourier cuts of those root involutions are honest complex
projections.  What cannot be done is interpret the printed Leavitt `star`
as Hilbert-space adjoint before the finite root-character coefficient corner
has been recovered.

The new raw cut

\[
 e=(1-r)/2,
 \qquad \tau(e)=1/2,
\]

remains valid because `r` is itself an order-two group element.  The next
valid question is whether the root-character/Pauli disintegration can place
the hard certificate and this trace-half raw cut in one finite multiplicity
corner.  Any proof which substitutes `q^star` by `Q^*` before that step
repeats `(HSI3)`.

## Replay

The exact audit is

```text
experiments/atlas_hard_star_vs_group_inverse.py
```

with committed output

```text
experiments/atlas-hard-star-vs-group-inverse.json
```

It uses exact characteristic-two prefix arithmetic and no numerical
tolerances.
