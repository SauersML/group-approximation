# Adaptive tensor amplification with a linear dimension cost

Date: 2026-08-19.

Provenance: developed in this GPT-5.6 Sol session; Wolfram was used only for the symbolic inequality sanity check recorded below.

This is an elementary companion to the repository's sharper exterior-power
profile.  It does not solve MF => hyperlinear, but it gives a transparent
sufficient rate and fixes the scalar-phase failure of raw tensor powers.

## Matrix lemma

Let `z in U(d)` with `||z-1||>=delta>0`.  Pad by an equal identity block:

```text
z'=z directSum 1_d.
```

Choose an eigenvalue `lambda` of `z` at distance at least `delta` from `1`.
If `m=tr_(2d)(z')`, the variance identity for the `2d` unit-circle
eigenvalues says

```text
1-|m|^2=(1/(2d)) sum |mu_j-m|^2.
```

Among those eigenvalues are `lambda` and `1`.  The parallelogram/minimum-center
identity gives

```text
|lambda-m|^2+|1-m|^2 >= |lambda-1|^2/2 >= delta^2/2,
```

hence

```text
1-|m|^2 >= delta^2/(4d).
```

Set `p=ceil(8d/delta^2)`.  From
`sqrt(1-x)<=exp(-x/2)` on `[0,1]` we obtain `|m|^p<=e^-1`.  Since tensor
normalized traces multiply,

```text
||(z')^(tensor p)-1||_2^2 >= 2(1-e^-1).
```

Wolfram was used only as a symbolic sanity check of
`sqrt(1-x)<=exp(-x/2)` for `0<=x<=1` and the positivity of the final constant;
the proof above is elementary.  Numerically the separation constant is about
`1.1243847729568`.

## Approximate representations

For a unitary-valued approximate representation `V`, identity padding keeps
operator multiplicative defects unchanged.  Tensor telescoping multiplies a
defect by at most `p`.  Therefore a local model of dimension `d`, defect
`epsilon` and operator separation `delta` becomes a local Hilbert--Schmidt
model with uniform separation and defect at most

```text
ceil(8d/delta^2) epsilon.
```

The same exponent works for all pairs in the window because the proof uses
only `d` and the common separation lower bound.  This avoids the normalized
2-norm dilution that would arise from taking a direct sum of pair-specific
amplifiers.

Thus a selectable MF family satisfying `d_n epsilon_n->0` is hyperlinear.
The condition is deliberately not confused with the sharper open profile
`epsilon_n^2/kappa_n->0`: operator separation only forces
`kappa_n=Omega(1/d_n)`, so that route asks only `epsilon_n sqrt(d_n)->0` in
the worst case.  The tensor criterion pays a linear rather than square-root
dimension cost, consistent with the universal-amplifier lower bounds already
recorded in `FALSE_FERMIONIC_AMPLIFICATION.md`.
