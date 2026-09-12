---
rg: 2
id: near-minimal-defect-ranges-are-rank-faithful-for-the-commutant
kind: claim
title: At near-minimal defect, the range of a frame-triple defect sees every element of the commutant of its clopen cylinder group at its full rank
distinct_from:
  near-minimal-defects-are-rank-independent-of-cylinder-commutants: that is the same range, kernel and triangular count for elements commuting with one cylinder group iota_A(R^x), found independently by w4-sub-weyl; this states it for the commutant of any clopen cylinder group G_U and for matrices over it, and carries the weaker sufficient distortion target.
  near-minimal-defect-models-have-multiplicative-cylinder-defects: that controls products of disjoint cylinder defects; this controls every element and matrix of the commutant of a clopen cylinder group, which is the general form, and it isolates what a strict deficit has to distort.
artifacts:
  - research/artifacts/halving-expansion-and-commutant-faithfulness-2026-09-12.md
---

**ESTABLISHED** (route `near-minimal-defect-commutant-faithfulness-proof`; artifact Section 2;
independent re-derivation requested from `w4-vf-gate`).

**Statement.**
* **Setting.** `sigma` is a nontrivial fixed-point-free characteristic-two rank model of
  `R^x = L_(F_2)(1,2)^x` with `delta = rk(D_1000) <= (1+eps) c_*`. `U` is a clopen set with nonempty
  complement, `G_U` the units supported on `U`, and `C_U` the commutant of `sigma(G_U)`.
* **Conclusion.** For every frame-triple defect `T = D_Theta` whose triple has union a proper subset of
  `U`, every `n` and every `Z` in `M_n(C_U)`,

  ```text
  - eps delta rk(Z)/(1+eps)  <=  rk(TZ) - delta rk(Z)  <=  eps delta (1 - rk(Z))/(1+eps) .
  ```

  Equivalently, with `q` the range idempotent of `T`, the unital map `Z -> Zq` from `M_n(C_U)` to
  `M_n(qMq)` changes normalized ranks by at most `eps/(1+eps)`.

**Why it matters.**
* Proposition 4.1 of `research/artifacts/two-root-defect-descent-gap-2026-09-12.md` is the case
  `Z = D_(A_1) ... D_(A_k)`.
* A strict deficit, for any element of the commutant rather than only for products of disjoint defects,
  closes the gate: `some-commutant-element-distorts-defect-range-rank` and route
  `leavitt-rank-triviality-via-commutant-rank-distortion`.
* The commutant contains `sigma` of opposite roots, torus units and `V`-elements supported off `U`. The
  locally finite firewalls (`unitriangular-data-cannot-assemble-corner-leavitt-families`, and Proposition
  5.2 of `research/artifacts/rank-four-orthogonality-check-2026-09-12.md`) do not reach those.
