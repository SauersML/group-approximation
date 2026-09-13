---
rg: 2
id: leavitt-units-admit-no-bounded-block-monomial-hs-model
kind: claim
title: Every block-monomial HS model of the binary Leavitt unit group has trivial permutation part, and no regular one has bounded blocks
distinct_from:
  leavitt-regular-atlas-block-monomial-gap: that bounds explicit A8-atlas transports in U(k) wr Sym(A_8) by a numerical gap; this excludes every regular block-monomial HS model of the whole group for every bounded k, with no atlas and no numerical constant.
  monomial-rank-models-are-hamming-models: that excludes monomial rank-metric models over finite fields by comparing rank with Hamming; this excludes Hilbert--Schmidt models with continuous U(k) labels, where HS is not comparable with Hamming on the labels and the trace has to be used.
  leavitt-unit-group-has-only-trivial-sofic-morphisms: that is about homomorphisms into universal sofic groups; this transfers it through the permutation-part homomorphism to every block-monomial unitary model.
artifacts:
  - research/artifacts/ex-q34-frame-extraction-2026-09-12.md
---

**ESTABLISHED.**  Let `R = L_(F_2)(1,2)` and let `W_omega` be a metric
ultraproduct of block-monomial groups `U(k_m) wr S_(n_m)` with normalized HS
distance.

1. **Trace-free rigidity.**  For every homomorphism `rho : R^x -> W_omega`,
   with arbitrary block sizes and no trace hypothesis, the permutation-part
   homomorphism `R^x -> prod_omega (S_n, d_H)` is trivial.  Every
   block-monomial HS model of `R^x` is asymptotically block-diagonal: the
   blocks are never moved.
2. **No bounded frames.**  No group containing `EL_9(R)`, in particular `R^x`,
   has a regular HS model in `U(k) wr S_n` for a fixed `k`.  For `k = 1` this
   means no regular microstates approximately normalize a full masa.

Consequence for `binary-leavitt-unit-group-hyperlinear`: every hyperlinear
model, if one exists, is **frame-incoherent**.  No full masa is approximately
normalized, and no decomposition into bounded-dimensional blocks is
approximately permuted.  All the approximation must live in blocks of
unbounded dimension that the permutation skeleton never moves.  This fences
every construction that glues fixed-size internal pieces (Pauli packets,
bounded Weyl or Heisenberg cells, finite-fibre rotations) along a permutation
skeleton, whatever the phases.

## Attempts

Established; see `leavitt-units-no-bounded-block-monomial-model-proof`.
