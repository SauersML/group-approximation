---
rg: 2
id: loop-braid-one-ring-push-mutual-link-is-not-family-member-proof
kind: route
title: "Exclude c-meeting types by the clasp homomorphism e_vc − e_vd − e_wc + e_wd; separate A_ca[(a,d)] from lk(A_vc b0) by the invariant sets {c_v ≠ c_w} and {c_a = c_d, others 1} of Fox 3-colorings"
target: loop-braid-one-ring-push-mutual-link-is-not-family-member
requires:
  - pure-loop-braid-group-is-colimit-of-cabling-stabilizers
artifacts:
  - research/artifacts/zp-loop-braid-one-ring-push-fox-coloring-obstruction-2026-09-19.md
  - research/artifacts/zp-loop-braid-descending-links-model-2026-09-13.md
  - experiments/loop-braid-one-ring-push-2026-09-17/fox_certificate.py
---

The complete hand proof is artifact §1. It is unreviewed.

Inputs:
- The cabling-subgroup generators and the strict fundamental domain, from
  `pure-loop-braid-group-is-colimit-of-cabling-stabilizers`. These give the criterion:
  `p[τ] ∈ lk(g b0)` iff `g^{-1}p ∈ P_b0 P_τ`.
- The conjugator exponent homomorphism e, from the descending-links model artifact §3.

1. **Item 1 (type exclusion).** A common vertex `s[z]` with `z ∋ c` would force
   `A_vc^{ε} ∈ P_b0 P_z P_b0`. But `λ = e_vc − e_vd − e_wc + e_wd` vanishes on the generators of
   `P_b0` and of `P_z`, while `λ(A_vc^ε) = ε`.
2. **Item 2 (Fox certificate).**
   - `A_ca ∈ P_b0`, so `u = A_ca[(a,d)] ∈ lk(b0)`, and u avoids c.
   - P acts on Fox 3-colorings `c ∈ F_3^n` on the right. The generators act as follows:
     - `A_ij : c_i ↦ 2c_j − c_i`;
     - `θ_k : c_k ↦ c_k ± 2(c_a − c_b)`;
     - `ζ_q : c_a, c_b ↦ 2c_q − (·)`.
   - `D = {c_v ≠ c_w}` is `P_b0`-invariant.
   - `S = {c_x = 1 for x ∉ {a,d}, c_a = c_d}` is `P_(a,d)`-invariant.
   - Take `ρ = (0,1,2,0,0; 1,…) ∈ D`, in the order `(c_v, c_w, c_c, c_a, c_d; others)`. Then
     `ρ·(A_vc^{−ε} A_ca) = (1,1,1,0,0; 1,…) ∈ S`.
   - So `A_vc^{−ε}A_ca = hk` would put `ρ·h` in `S ∩ D = ∅`. Hence `u ∉ lk(A_vc^ε b0)`.

`fox_certificate.py` recomputes the certificate by full orbit enumeration for n = 5..10.
`orbit_test.py` runs an independent finite-orbit scan with S3, D4 and A4, including sanity checks
and a control against the ESTABLISHED pair-twist mutual link.
