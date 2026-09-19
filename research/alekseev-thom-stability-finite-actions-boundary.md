---
rg: 2
id: alekseev-thom-stability-finite-actions-boundary
kind: claim
title: Alekseev-Thom residual amplification and the normal-subgroup boundary for stability in finite actions
artifacts:
  - research/artifacts/alekseev-thom-2512.15494-verified.md
distinct_from:
  sofic-stable-implies-residually-finite: that is the general consequence of stability in finite actions for a sofic actor; this records the current primary literature's residual-amplification lemma, open boundary, and normal-kernel limitation.
  gkp-sofic-action-toolkit: that concerns soficity of set actions and locally finite stabilizers; this concerns weak containment of pmp limits of sofic approximations.
---

The current primary text of Alekseev--Thom, *Remarks on approximability and
stability for groups*, arXiv:2512.15494v1, supplies three precise facts used
in the arithmetic action audit:

1. Lemma 3.2: if `G` is residually finite, every asymptotic homomorphism
   `alpha_n:G->Sym(X_n)` can be multiplied by regular actions of separating
   finite quotients so that

   ```text
   theta_n(g)(x,h)=(alpha_n(g)x, lambda(q_n(g))h)
   ```

   is a sofic approximation, and the original asymptotic action remains a
   factor under first-coordinate projection.
2. Theorem A(ii)/Theorem 3.4 passes stability in finite actions from `G` to
   `G/N` when `N` is a Kazhdan **normal** subgroup (with the other printed
   hypotheses).  It gives no theorem for a nonnormal commensurated subgroup.
3. The introduction states that it is open whether a residually finite group
   not stable in finite actions exists.

Thus this paper supports the residual amplification in the coset proof, but
does not establish stability for `SL_3(Z[1/p])` and does not use the
nonnormal pair `SL_3(Z)<SL_3(Z[1/p])` to do so.

DERIVATION
alekseev-thom-stability-finite-actions-citation
