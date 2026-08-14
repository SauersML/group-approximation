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

## 3. Coarse covariance versus fine fiber variance

This does not make the transition variance vanish automatically. Let
`alpha:F->G` be the finite coefficient homomorphism implemented by the
compressor. A repaired exact `alpha`-intertwiner sends a source character
cut `P_chi` into the coarse target cut

```text
R_chi=sum_(zeta: zeta composed_with alpha=chi) Q_zeta. (TGI8)
```

Therefore the transported projection commutes with the coarse PVM
`(R_chi)`. But it may retain off-diagonal matrix coefficients between two
different target characters `zeta` having the same restriction to `F`.
Those coefficients are exactly the proper-extension-fiber variance.

Homomorphism twirling controls leakage between distinct coarse fibers with
dimension-free constants. It cannot distinguish characters inside one
fiber, because they are identical on `alpha(F)`. The remaining mixed
multiplication theorem is precisely the fine-fiber refinement

```text
coarse alpha-intertwining
 + cross-root multiplication
 -> commutation with every fine Q_zeta.              (TGI9)
```

## 4. Consequence for the research program

The previous research map mixed two different issues:

1. arbitrary commutant gauges in a chosen regular-basis coefficient
   expansion; and
2. intrinsic fine-character variance of the transported source projection.

Equation `(TGI2)` shows that issue 1 cancels from issue 2 exactly. The
compiled compressor word may still be required to synchronize several
edges or whole-map decoders, but it is not required to pin a source gauge
before proving a single-edge transition-variance estimate.

The corrected smallest live theorem is:

> **Fine-fiber multiplication gate.** For the actual proper Leavitt
> coefficient inclusion, use the cross-root multiplication relations to
> show that the transported coarse source cut is asymptotically block
> diagonal for the fine target-character PVM, with total Hilbert--Schmidt
> error tending to zero.

This statement is invariant under every source-commutant gauge and therefore
cannot be falsified by the `C_2` deformation in
`FALSE_PURE_FOUR_ROOT_WORDS_CANNOT_PIN_COMPRESSOR_GAUGE.md`. Its exact
countermodels must instead retain nonzero coherence inside an extension
fiber while satisfying the mixed multiplication packet.
