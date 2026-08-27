---
rg: 2
id: corner-renormalization-cost-proof
kind: route
title: Two lines of trace bookkeeping and the recorded functorial bound
target: corner-renormalization-cost
requires: []
artifacts:
  - notes/FALSE_FERMIONIC_AMPLIFICATION.md
  - notes/FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md
---

## Direct proof

`(C1)` is `||axb||<=||a|| ||x|| ||b||` with `a=b=p`.

For `(C2)`, traciality gives `||xb||_(2,tau)^2 = tau(b^* x^* x b)
= tau(x^* x b b^*) <= ||b||^2 ||x||_(2,tau)^2` and
`||ax||_(2,tau)^2 = tau(x^* a^* a x) <= ||a||^2 ||x||_(2,tau)^2`, so
`||pxp||_(2,tau) <= ||x||_(2,tau)`.  Since
`||y||_(2,tau_p)^2 = tau(y^* y)/tau(p) = ||y||_(2,tau)^2/tau(p)` for
`y in pAp`, this is `(C2)`.  If `x = pxp` both inequalities used are
equalities, so the constant is attained.

`(C3)` is the chain `Tr(A^*A) <= ||A||_op Tr(|A|) <= 2 Tr(|A|)` divided by
`r >= 1`; it is stated in section 4 of
`notes/TRUE_SCHATTEN_ONE_RADICAL_CORNER.md` as the scaling boundary of that
theorem.

The identification of the constant in the matrix case is arithmetic:
`tau(p)=r/d` for a rank-`r` projection under the normalized trace.  The
comparison with the functorial lower bound is the statement of Theorem 5 of
`FALSE_FERMIONIC_AMPLIFICATION.md`, whose complete proof (Rademacher
averaging over `floor(d/r)` orthogonal rank-`r` blocks against the
`2`-norm Lipschitz constant of a continuous homomorphism `U(d)->U(N)`) is
recorded in that artifact; and the profile `epsilon_n sqrt(d_n/r_eff)` is
equation `(ERP4)` of `FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md`.  End proof.

## Consequence

An operator-norm almost representation may be compressed to a corner of
vanishing relative rank with no loss, and the corner is measured by its own
normalized trace; this is what makes
`mf-finite-normal-tracially-visible`, the central-sign criterion, and the
finite-normal cancellation work.  A normalized-Hilbert--Schmidt almost
representation cannot be so compressed: the same step multiplies its defect
by `tau(p)^(-1/2)`.  Every known attempt to move the non-MF architecture to
the tracial side dies at exactly this factor.
