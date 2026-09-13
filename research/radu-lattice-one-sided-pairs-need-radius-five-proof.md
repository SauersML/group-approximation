---
rg: 2
id: radu-lattice-one-sided-pairs-need-radius-five-proof
kind: route
title: Square the defect idempotent on the residual coincidences of the radius-four ball
target: radu-lattice-one-sided-pairs-need-radius-five
requires:
  - radu-lattice-one-sided-pairs-need-residual-coincidences
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
artifacts:
  - research/artifacts/radu-lattice-radius-four-linear-pairs-2026-09-12.md
---

## Why sufficient

1. **Short residual elements** (artifact §0). Remark 3.6, imported by
   `radu-bmw-lattice-embeds-in-titz-witzel-kernel`, lists `delta^(+-4)` as the only nontrivial
   elements of length at most eight in `ker Phi`. `Phi(Gamma')` is finitely generated linear, so it is
   residually finite, and `Gamma_0`, which lies in `Gamma'`, lies in `ker Phi`. So `Gamma_0 ∩ B_8 ⊆ {1, delta^(+-4)}`.
   Membership `delta^4 in Gamma_0` is not used.
2. **Coincidences in `B_4`** (§1). Square moves preserve the horizontal and vertical letter counts, so a
   geodesic word for a vertical element is its reduced word in `x, y, z`. A coincident pair in `B_4` is a
   geodesic split of `xzxzxzxz`, so it is `{delta^2, delta^(-2)}`.
3. **Item 1** (§2). Normalize by `(u^(-1) A w^(-1), w B u)`. `D = I_n - A B` is idempotent. `D` vanishes
   modulo `Gamma_0` over any field: the residually finite quotient separates the finite support of the
   image of `D` into a finite group, where matrix algebras are finite-dimensional and directly finite.
   This is item 1 of `radu-lattice-one-sided-pairs-need-residual-coincidences` over `K`. So
   `D = E (delta^2 - delta^(-2))`, and `D^2 = E^2 (delta^4 - 2 + delta^(-4))` has disjoint support, so
   `E = 0`.
4. **Item 2** (§3). Points of `B_k` alone in their coset have coefficient zero. The coefficient of `D^2`
   at a point of `C_k` is a sum over factorizations inside `C_k`.
5. **Item 3** (§4.1–4.2). The normal form `h = alpha (omega delta^4)` and the length of the cancelling
   suffix give the `delta^(+-4)` pairs in `B_5`. H10 adds only `{delta^2 y, delta^(-2) y}`. Pushing
   `a, b, c` through `Omega` keeps `Omega`, and a case check in `<x,z>` together with the position of
   `y` gives `Omega Omega ∩ Omega = ∅`.
6. **Item 4** (§4.3). `(zx)^(-1) (xz)^3 = delta^4` and `(xz)^(-1) (zx)^3 = delta^(-4)`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 45 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS, given Remark 3.6. Items 1–6 re-derived on paper:*
- *Lemmas 1.1–1.2;*
- *Theorem A, steps 1–5;*
- *Lemma B;*
- *Lemmas 4.1–4.2, with the twisting rules and the exponent sets.*

*Theorem C and item 3 stay conditional on H10. In the last case of Lemma 4.1 the two parenthetical reasons are swapped; the conclusion is unaffected.*
