# Intrinsic transition variance is source-gauge invariant

Date: 2026-08-14

## 1. Outcome

The source-commutant gauge obstructing coefficient expansions is irrelevant
to the intrinsic transition-effect variance.

Let `P` be a source projection, `(Q_j)` a target PVM, `U` the actual
compressor, and `C` a unitary with `[C,P]=0`. Put

```text
E_U=U P U*,
A_j(U)=P U* Q_j U P.                                (TGI1)
```

Then

```text
E_(UC)=E_U,
A_j(UC)=C* A_j(U) C.                                (TGI2)
```

Consequently every spectral quantity of each effect, its idempotence defect,
and the total transition variance are unchanged:

```text
sum_j tau_P(A_j(UC)-A_j(UC)^2)
 =sum_j tau_P(A_j(U)-A_j(U)^2),                     (TGI3)

sum_j ||[E_(UC),Q_j]||_2^2
 =sum_j ||[E_U,Q_j]||_2^2.                          (TGI4)
```

Thus the intrinsic transition route has already quotiented out the arbitrary
source multiplicity gauge. It does not need the coproduct-classification
theorem merely to define or control its single-edge variance.

## 2. Proof

Commutation and unitarity give

```text
(UC)P(UC)*
 =U(CPC*)U*
 =UPU*.                                              (TGI5)
```

Similarly,

```text
P(UC)*Q_j(UC)P
 =PC*U*Q_jUCP
 =C*(PU*Q_jUP)C.                                    (TGI6)
```

If `A'=C*AC`, then

```text
A'-(A')^2=C*(A-A^2)C.                               (TGI7)
```

Trace invariance proves `(TGI3)`, while `(TGI4)` follows immediately from
the first identity in `(TGI2)`.

The matrix identities `(TGI5)--(TGI7)` are transcribed source-first in
`GroupApproximation/Sofic/TransitionGaugeInvariance.lean` as

```text
transportedProjection_mul_commutant_eq
transitionEffect_mul_commutant_eq_conj
conj_idempotenceDefect.
```

No local build or computation was run.

## 3. Actual-unitary covariance closes the single-edge variance

Let `alpha:F->G` be the finite coefficient homomorphism implemented by the
compressor. The coarse target cut is

```text
R_chi=sum_(zeta: zeta composed_with alpha=chi) Q_zeta. (TGI8)
```

For the actual unitary compressor, Fourier expansion gives directly

```text
||U P_chi U*-R_chi||_2^2
 <= average_a ||U rho(a) U*-sigma(alpha(a))||_2^2.  (TGI9)
```

Because `R_chi` is already a sum of fine target cuts, orthogonal projection
onto the fine block-diagonal algebra bounds the total fine commutator energy
by twice the right side of `(TGI9)`. See
`TRUE_COVARIANCE_CONTROLS_TOTAL_TRANSITION_VARIANCE.md`.

The earlier apparent within-fiber obstruction applies to an arbitrary
nonunitary twirled intertwiner, whose range may be a proper subspace of
`R_chi`. It does not apply to conjugation of the explicit Fourier cut by the
actual unitary `U`.

## 4. Consequence for the research program

The previous research map mixed two different issues:

1. arbitrary commutant gauges in a chosen regular-basis coefficient
   expansion; and
2. compatibility of the fine-character transition PVMs belonging to
   different compressor/root occurrences.

Equation `(TGI2)` shows that issue 1 cancels before issue 2 is considered,
and `(TGI9)` closes each single edge. The compiled compressor word may still
be required to synchronize several edges or whole-map decoders.

The corrected smallest live theorem is:

> **Multiplication-compatible transition-PVM gate.** Use the cross-root
> multiplication relations to put the individually rounded transition PVMs
> for all required adjacent-root occurrences on one common classical
> multiplicity coordinate, with their labels obeying the Leavitt product
> table up to vanishing total error.

The fixed Pauli model shows why separate exact PVMs are insufficient: the
measurements attached to different edges can remain noncommuting even though
every individual covariance and transition statement is exact.
