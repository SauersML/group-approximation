---
rg: 2
id: sl3z-lattice-space-action-is-sofic
kind: claim
title: SL_n(Z) acting on the space SL_n(R)/SL_n(Z) of unimodular lattices is sofic for every n >= 2, with Hecke orbits as finite models
distinct_from:
  induced-actions-sofic-iff-homogeneous-action-sofic: that proves the homogeneous action controls soficity of every induced action; this proves the homogeneous action is sofic, so for SL3(Z) induction preserves soficity in both directions
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that concerns SL3(Z[1/2]) on a compact quotient of the 2-adic group, where SL3(Z) acts profinitely; this is the real place, a mixing action, handled by equidistribution of Hecke orbits
artifacts:
  - research/artifacts/sl3z-lattice-space-hecke-sofic-2026-09-12.md
  - research/artifacts/sl3z-lattice-space-hecke-sofic-part2-2026-09-12.md
---

**ESTABLISHED (unreviewed).** For every `n >= 2`, the left action of `SL_n(Z)` on
`X_n = SL_n(R)/SL_n(Z)`, with its invariant probability `μ`, is sofic (Păunescu Definition 1.4). For
`n = 3` this refutes `sl3z-lattice-space-action-is-not-sofic`.

**Finite models.** Fix a prime `p` and put `a_k = diag(p^k, p^(−k), 1, ..., 1) ∈ SL_n(Z[1/p])`. The
point `a_k^(−1)SL_n(Z)` lies in the image of the commensurator. So its orbit
`V_k = SL_n(Z)·a_k^(−1)SL_n(Z)` is finite: a Hecke orbit of the base lattice `Z^n`.
**Lemma E:** the normalized counting measures on `V_k` converge to `μ` against `C_c(X_n)`. Then
`finite-equidistributed-orbits-give-sofic-action` applies. For odd `n` the orbits `V_k` are themselves
asymptotically free, so they alone are sofic models (part 2 artifact, Section 6).

**Why it holds.** A point `g·SL_n(Z)` has finite orbit iff `g` commensurates `SL_n(Z)`, and the
commensurator, which contains `SL_n(Q)`, is dense in `SL_n(R)`. Mixing of `SL_n(Q_p)` on the S-arithmetic cover
`(SL_n(R) × SL_n(Q_p))/SL_n(Z[1/p])` makes those orbits equidistribute. The action is mixing, yet it is
approximated by its own periodic orbits. The mechanism is arithmetic.

**Consequences.**
1. `sl3z-nonsofic-action-from-lattice-space-action` and
   `mixing-nonsofic-action-from-sl3z-lattice-space-action` can never fire.
2. Condition 1 of `induced-actions-sofic-iff-homogeneous-action-sofic` holds for
   `SL_3(Z) <= SL_3(R)`. Combined with `howe-moore-lattice-nonsofic-action-transfers-to-mixing`: for an
   ergodic seed `Z`, the free mixing action `SL_3(R) ×_(SL_3(Z)) (Z × {0,1}^(SL_3(Z)))` is sofic iff
   `Z` is. So a nonsofic mixing witness for `SL_3(Z)` must come from a nonsofic seed.
3. For a lattice `Λ` of `SL_3(R)` not commensurable with any conjugate of `SL_3(Z)`, for instance a
   cocompact one, the Hecke mechanism is structurally blind. Every `SL_3(Z)`-orbit on `SL_3(R)/Λ` is
   infinite, and an extension has finite orbits only above finite orbits (part 2 artifact, Section 8).
   Next candidate: `sl3z-on-cocompact-lattice-quotient-is-not-sofic`.

**Model test.** `n = 2` agrees with Păunescu's class: `SL_2(Z) = Z/4 *_(Z/2) Z/6` lies in it by
Theorem 3.9 (`paunescu-sofic-action-class-permanence`).

**Credit and trust.** Equidistribution of Hecke points is classical (Clozel--Oh--Ullmo 2001, Eskin--Oh
2006; theorem numbers not verified), and the thickening device is Margulis's and Eskin--McMullen's. The
artifact proves the needed case from Howe--Moore alone. Soficity as a consequence has had only a
bounded novelty check (web-search budget exhausted, arXiv API unreachable) and may be folklore.
Unreviewed.

Proof in `sl3z-lattice-space-action-is-sofic-proof`.
