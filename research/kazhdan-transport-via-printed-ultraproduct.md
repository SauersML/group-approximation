---
rg: 2
id: kazhdan-transport-via-printed-ultraproduct
kind: route
title: The manuscript's printed ultraproduct road, KT.01 through KT.11
target: kazhdan-asymptotic-commutant-transport
requires: [printed-ultraproduct-ambient-for-kazhdan-transport]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/UltraproductAdjointAmbient.lean
  - GroupApproximation/Sofic/UltraproductDedekindFinite.lean
  - GroupApproximation/Sofic/UltraproductKazhdanProjection.lean
  - GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean
---

## Why sufficient

This is a **second** route into the transport theorem, and it exists to record
the *printed* road rather than to change the target's status: the target is
already established by the quantitative finite-stage proof of Appendix
`app:finite-stage` (see [[kazhdan-asymptotic-commutant-transport-proof]]).
What this route adds is that the argument the manuscript actually prints is
being checked step by step.

**Certification status, 2026-08-16.**  KT.01 and KT.03--KT.09 are in the root
build and elaborate.  KT.10 and KT.11, together with the by-contradiction
skeleton, are written in `Sofic/UltraproductKazhdanTransport`, which **does not
currently elaborate** — unknown projections on the ambient bundle, an unsolved
goal in the descent, and a field-notation failure on `kt_11_descend` — so that
module is out of the build and out of this node's `artifacts:`.  Its declaration
names are kept in the ledger below because they are the intended targets, not
because they are certified; the honest reading of this route today is
"KT.01--KT.09 checked, endgame drafted, ambient missing".

The manuscript's own ledger of the printed proof, with the Lean location of
each step:

```text
KT.01  adjoint model K_n = L^2(M_{d n}, tr_{d n}), Ad U_n(g) xi = U_n(g) xi U_n(g)*
       -> UltraproductAdjointAmbient.kt_01_hsNormSq_rowVec, kt_01_adjoint_action,
          kt_01_hsNormSq_adjoint, kt_01_adjoint_asymptoticallyMultiplicative
KT.02  the Hilbert-space ultraproduct K_omega
       -> OPEN, the prerequisite of this route
KT.03  the norm ultraproduct B_omega = prod_omega B(K_n) acting on K_omega
       -> UltraproductAdjointAmbient.adjointNormCorona (the algebra half);
          the action is part of the prerequisite
KT.04  faithfulness, hence ran P subset ran Q  =>  P <= Q
       -> UltraproductAdjointAmbient.kt_04_norm_eq_limsup,
          kt_04_absorb_of_range_le, kt_04_range_le_of_absorb
          (the absorption dictionary; faithfulness is part of the prerequisite)
KT.05  pi : H -> U(B_omega), pi g = [Ad U_n g]_omega, is a homomorphism
       -> UltraproductAdjointAmbient.adjointCoronaHom
KT.06  B_omega is finite: sigma* sigma = 1 => sigma sigma* = 1
       -> UltraproductDedekindFinite.kt_06_ultraproduct_finite, and the stronger
          instance normMatrixCStarCorona_isDedekindFiniteMonoid
KT.07  the Kazhdan spectral gap for the averaged operator h
       -> UltraproductKazhdanProjection.kt_07_kazhdan_gap, kt_07_spectrum_subset
KT.08  the Kazhdan projection P, with ran P = Fix
       -> UltraproductKazhdanProjection.kt_08_kazhdan_projection
KT.09  V = pi s, Q = V P V*, Fix subset V.Fix, i.e. P <= Q
       -> UltraproductKazhdanProjection (the compression identities)
KT.10  r = V*Q, sigma = r + (1 - Q) is an isometry; finiteness makes it unitary,
       and sigma sigma* = P + (1 - Q) forces Q = P
       -> UltraproductKazhdanTransport.kt_10_isometry_identities,
          kt_10_finiteness_reverses (calculation in
          Analysis/ProperIsometryFromCompression)
KT.11  xi = [xi_n]_omega is fixed by every pi(iota gamma); Q = P puts V xi in Fix,
       which is the asserted Hilbert--Schmidt vanishing along omega
       -> UltraproductAdjointModel.kt_11_descend
```

The by-contradiction skeleton the manuscript runs around this ledger is
`ultraproductKazhdanTransport` (drafted, not yet elaborating — see the status
note above): if the conclusion fails there are `gamma_0`,
`delta > 0` and an infinite `I` on which the conjugated commutator has
normalized Hilbert--Schmidt norm at least `delta`; a free ultrafilter `omega`
with `I` in `omega` is fixed; KT.11 makes the commutators vanish along
`omega`; `I` in `omega` is contradicted.  Since the failing subsequence was
arbitrary, the full sequence converges.  In the manuscript's own coordinates
this is `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport_ultraproduct`,
which lands in `Sofic/ManuscriptKazhdanTransport` once the module above does.

Two things are worth flagging because they are places a formalization could
have cheated and did not.  The constant is the printed one: the abstract
spectral-gap lemma available in the repository gives only
`1 - eps^2/(4|S|)`, and `manuscript_eigenvalue_le_of_ne_one` re-runs the
manuscript's quadratic-form estimate to recover `1 - kappa^2/(2|S|)`.  And
`kappa <= 1` is never assumed, because the printed argument never needs it.

## Why the single prerequisite is not a restatement of the target

The prerequisite asserts the existence of one object — a Hilbert-space
ultraproduct of matrix `L^2` spaces with a faithful action of the operator-norm
corona.  It mentions no Kazhdan group, no compression, and no commutator, and
it can fail (or be unformalizable at a given Mathlib revision) while the
transport statement stays true, as it in fact does here.  Conversely, granting
it does not restate the target: everything in the ledger above is still an
argument, and KT.06--KT.11 are where the mathematics happens.
