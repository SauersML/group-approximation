---
rg: 2
id: non-central-involution-formal-involution-proof
kind: route
title: Use N = 1 + s as both control and target, with a quadratic middle rule
target: non-central-involutions-carry-nonaffine-formal-involutions
requires:
  - zero-divisor-shears-are-formal-automorphisms
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

Artifact, Section 3, Corollary 6.
1. **The control.** `N = 1 + s` has `N^2 = 1 + 2s + s^2 = 0` in `F_2[G]`, and `L_N x = S`.
2. **The shear.** With `Gamma(z)(h) = z(h) z(hm)`, `L_N(Gamma(S))(h) = S(h)S(hm) + S(hs)S(hsm)`. Since
   `S(hs) = S(h)`, this is `S(h)(S(hm) + S(hsm))`. So `tau` is the zero-divisor shear with `A = B = N`,
   and it is its own formal inverse in characteristic two.
3. **Distinct cells.** Coincidences among `hm, hms, hsm, hsms`, or with `h, hs`, force `m = 1`, `m = s`
   or `sm = ms`. Each of these contradicts `m^(-1) s m ≠ s`.
4. **Non-affine.** A multilinear representative over `F_2` is unique, and this one has degree two.
