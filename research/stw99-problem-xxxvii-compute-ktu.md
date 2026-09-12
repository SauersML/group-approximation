---
rg: 2
id: stw99-problem-xxxvii-compute-ktu
kind: claim
title: Compute the classification invariant of classifiable crossed products (STW Problem XXXVII)
root: true
artifacts:
  - research/artifacts/stw99-dynamics-cluster-2026-08-30.md
---

**Problem XXXVII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(explicitly vast in scope): compute `KT_u(C(X) ⋊ G)` for the actions
producing classifiable algebras.  Encoded here as the closed endpoint
STW isolate as the bottleneck: a general method computing the PAIRING
`ρ : K_0 → Aff(T)` for classifiable crossed products, extending
Pimsner's free-group method.

## Attempts

* K-groups (Pimsner--Voiculescu, Baum--Connes/Meyer--Nest,
  Proietti--Yamashita spectral sequences) and traces (invariant
  measures, Ursu) are separately computable in wide generality; the
  pairing is the only component with a single known method (Pimsner,
  for free groups; the `Z` case written out as `Λ_τ` in Blackadar
  10.10.1).  The honest open shape: a Baum--Connes-compatible formula
  for `ρ` — the assembly map computes `K_0` from equivariant homology,
  invariant measures live on the same chain level (as transverse
  measures/Ruelle--Sullivan currents), and the pairing should be
  induced by their cap product.  For étale groupoids this is the
  content Matui's HK-conjecture circle handles in examples; a
  Ruelle--Sullivan cap-product theorem at the generality of amenable
  actions would close the problem's bottleneck.  Nothing that general
  is in the literature; the conjecture-shaped statement is recorded
  here so refutations (HK-style counterexamples DO exist — Scarparo)
  can be tested against it: Scarparo's HK counterexamples concern
  homology vs K-theory integrally, not the measure pairing, so they do
  not refute the cap-product formula for `ρ`.
