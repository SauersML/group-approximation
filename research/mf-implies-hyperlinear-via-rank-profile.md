---
rg: 2
id: mf-implies-hyperlinear-via-rank-profile
kind: route
title: Phase-cancelled amplification of a rate-controlled MF model
target: mf-implies-hyperlinear
requires: [hyperlinear-elementwise-visibility, mf-trace-gap-defect-ratio-models]
artifacts:
  - notes/FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md
  - notes/FALSE_FERMIONIC_AMPLIFICATION.md
  - notes/NOTEPAD.md
  - GroupApproximation/Sofic/ExteriorMFProfile.lean
---

## Why sufficient

Fix `g != 1` in the countable MF group `G` and take models `phi_n` with
`(P1)` from `mf-trace-gap-defect-ratio-models`.  Apply the trace-gap/defect
amplifier of `FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md`, Lemma 1:
the phase-cancelled model

```text
theta_n(g)=phi_n(g) directSum conjugate(phi_n(g))
           directSum 1 directSum 1,   Psi_n = theta_n^(tensor L_n),
```

with `L_n eta_n^2 -> 0` and `L_n kappa_n -> infinity` (possible exactly by
`(P1)`, since the normalized Hilbert--Schmidt defect `eta_n` is dominated by
the operator-norm defect `epsilon_n`), satisfies

```text
||Psi_n(a)Psi_n(b)-Psi_n(ab)||_(2,norm)^2 <= L_n eta_n^2/2 -> 0,
tr(Psi_n(g)) = (1-kappa_n/2)^(L_n) <= exp(-L_n kappa_n/2) -> 0.
```

So `g` is tracially visible with any constant `c_g<1`.  Doing this for each
`g != 1` and invoking `hyperlinear-elementwise-visibility` --- which is what
lets each element be handled by its own model --- makes `G` hyperlinear.

## Why the amplifier cannot be improved away

The rank-one case of `(P1)` is `epsilon_n sqrt(d_n) -> 0`, matching the full
exterior/Fock amplifier `G_d` of `FALSE_FERMIONIC_AMPLIFICATION.md`
(Lemma 3: `||G_d(U)-G_d(V)||_2 <= sqrt(d/2)||U-V||_op`; Lemma 2:
`|tr G_d(U)| <= 1-c^2/4` whenever `||U-I||_op >= c`, rank-free).  Theorem 5
of the same note proves the `sqrt(d)` loss is optimal among *all* continuous
homomorphisms `U(d)->U(N)`.  Hence no better universal matrix functor exists
and this route cannot be completed by improving the amplifier: only
`mf-trace-gap-defect-ratio-models` can complete it.

## Not a restatement of the target

The prerequisite is strictly stronger than `mf-implies-hyperlinear` and can
fail while the target holds.  It constrains *operator-norm* models by a rate,
and hyperlinearity supplies no operator-norm data at all: the Hilbert--Schmidt
models it provides cannot be combined with an MF model to produce one, since
tensor products and direct sums of the two are only Hilbert--Schmidt
asymptotically multiplicative.  It is moreover known to be false for some
model families --- by `sign-mark-rate-is-sector-density` it fails whenever
`(T)` squeezes a sign mark onto a sector of density `O(epsilon_n^2)` --- which
a reformulation of the target could not be.  The genuine step is the
amplifier below.

## Formalization status of the amplifier

The rank-one branch is essentially kernel-checked already, in
`GroupApproximation/Sofic/ExteriorMFProfile.lean`: exact multiplicativity and
unitarity of the phase-free amplifier (`exteriorAdMatrix_mul`,
`exteriorAdMatrix_mem_unitaryGroup`), the character identity
(`normTrace_exteriorAdMatrix`, `trace_fockMatrix`), the defect bound
`hsDistSq_exteriorAdMatrix_le` (`<= d eps^2/2`), the dimension-free
separation bound `sq_div_two_le_hsDistSq_exteriorAdMatrix` (`>= c^2/2`), and
the tensor-power versions used for boosting
(`hsDistSq_exteriorTensorMatrix_le`).  So the machine half of this route is
built; only the input rate is missing.
