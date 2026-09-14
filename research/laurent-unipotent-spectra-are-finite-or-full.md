---
rg: 2
id: laurent-unipotent-spectra-are-finite-or-full
kind: claim
title: For d >= 3, every representation of SL_d(F_q[t^±1]) has column unipotent spectrum finite or full, and finite spectrum means a congruence quotient
distinct_from:
  sln-z-unipotent-spectrum-finite-or-full-torus: that is the characteristic-zero dichotomy on the torus T^(d-1) for SL_d(Z); this is the positive-characteristic dichotomy on the profinite dual of F_q[t^±1]^(d-1), proved by an explicit window-density argument with no dynamics on tori.
  laurent-sl-n-representations-have-sl2-invariant-vectors: that is the finite-dimensional congruence theorem; this says which arbitrary unital C-star representations reduce to finite congruence quotients.
artifacts:
  - research/artifacts/sk-mf-laurent-2026-09-14-part1.md
---

**ESTABLISHED (unreviewed).** Let `q` be a prime power, `A = F_q[t,t^{-1}]` and `m ≥ 2`.

1. **Dichotomy.** A closed subset `K ⊆ Â^m` invariant under the dual action of `E_m(A)` is either finite, contained in
   `((A/J)^m)^` for a nonzero ideal `J`, or all of `Â^m`.
2. **Representations.** Let `d ≥ 3` and `σ : C*(SL_d(A)) → B` be a unital *-homomorphism into a unital C*-algebra. Let
   `K` be the joint spectrum of `σ(I + Σ_{i<d} v_i e_{i,d})`, `v ∈ A^{d-1}`. Either `K = Â^{d-1}`, or `σ` factors through
   `C*(SL_d(A/J))` for a nonzero ideal `J`.

**Model tests.**
- `m = 1` fails: the orbit of a character with zero annihilator is a closed, infinite, proper invariant set.
- The trivial representation has `K = {1}` and `J = A`.
- The regular representation has Haar spectrum, so `K` is full.

No novelty is claimed. The ingredients are elementary, plus Bass–Milnor–Serre Corollary 4.3.

Proof: `laurent-unipotent-spectra-finite-or-full-proof`.
