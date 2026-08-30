---
rg: 2
id: mf-hs-defect-gap-profile
kind: claim
title: Weak MF models admit an intrinsic HS-defect versus trace-gap profile
distinct_from:
  mf-trace-gap-defect-ratio-models: That claim requires the square of the operator-norm defect to beat the trace gap; this claim uses the weaker rate condition involving the actual normalized Hilbert--Schmidt defect, the quantity paid by the phase-cancelled tensor amplifier.
  mf-invariant-corner-visibility: That claim demands a dimension-free trace gap in operator-norm models; this claim allows the gap to vanish, provided it dominates the squared normalized Hilbert--Schmidt relation defect.
artifacts:
  - research/artifacts/weak-mf-hs-profile-audit-2026-08-30.md
---

Let `G` be a countable weak norm-corona MF group and let `g != 1`.  Choose
increasing finite windows `F_n` exhausting `G`, each containing `1` and `g`,
and unitary operator-norm local models

```text
phi_n : G -> U(d_n).
```

For the multiplication tests in `F_n`, put

```text
eta_n = max { ||phi_n(a) phi_n(b) - phi_n(ab)||_(2,norm)
              : a,b,ab in F_n },
kappa_n = 1-Re tr_(d_n)(phi_n(g)).
```

Then the models may be selected so that their operator-norm multiplication
defects tend to zero, `kappa_n>0` eventually, and

```text
eta_n^2 / kappa_n -> 0.                                      (HP1)
```

This is the intrinsic rate profile used by the phase-cancelled tensor
amplifier.  On any fixed sequence of models its rate condition is weaker
than the condition in the current open claim
`mf-trace-gap-defect-ratio-models`: if `epsilon_n` is the corresponding
operator-norm defect, then `eta_n <= epsilon_n`, so
`epsilon_n^2/kappa_n -> 0` implies `(HP1)`, but not conversely.
No strict separation of the two existential group properties is asserted.

Unlike the operator-defect profile, `(HP1)` is exactly unchanged by identity
padding.  If `phi_n` is replaced by `phi_n directSum 1_(m_n)` and
`rho_n=d_n/(d_n+m_n)`, then

```text
eta_n'^2 = rho_n eta_n^2,       kappa_n' = rho_n kappa_n,
eta_n'^2/kappa_n' = eta_n^2/kappa_n.
```

Thus arbitrary sparse realization of the marked word is not by itself an
obstruction to this claim.  A counterexample must force the relation error
to occupy Hilbert--Schmidt mass comparable to the marked trace gap in every
operator-norm model; mere growth of the ambient dimension or identity-block
padding cannot do so.

The claim is still genuinely open under the weak Carrión--Dadarlat--Eckhardt
convention.  Norm-corona injectivity controls a singular value of
`phi_n(g)-1`, while `(HP1)` compares two normalized second moments.  No
known selection theorem supplies that comparison.

## Attempts

**Identity padding does not refute the profile.**  The exact calculation
above shows that padding multiplies numerator and denominator by the same
relative dimension.  This removes the standard counterexample to the
operator-defect profile, but gives no positive selection mechanism.

**Spectral support and invariant hull.**  A spectral projection of
`phi_n(g)-1` captures the marked Frobenius mass, but need not approximately
commute with the other group letters.  Taking its invariant hull can spread
one marked direction through the whole coordinate space.  The established
draft `sparse-lamplighter-corona-has-no-visible-corner` makes the failure
exact in one faithful realization: every invariant corner has intrinsic
trace gap tending to zero.  Since the lamplighter has other trace-visible
models, this blocks arbitrary-realization extraction without refuting the
existential profile.

**Ultrafilter and trace selection.**  Passing to a norm ultraproduct on a
subsequence where `g` is operator-visible preserves the norm witness, but
the normalized coordinate trace can still kill it.  A rank-one reflection
has operator distance `2` and normalized `2`-distance `2/sqrt(d)`.  Thus an
ultrafilter alone does not produce `(HP1)`.
