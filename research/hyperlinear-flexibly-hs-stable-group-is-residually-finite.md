---
rg: 2
id: hyperlinear-flexibly-hs-stable-group-is-residually-finite
kind: claim
title: A finitely generated hyperlinear flexibly HS-stable group is residually finite
distinct_from:
  hyperlinear-hs-stable-is-residually-finite: that assumes strict same-dimension stability of a finitely presented group; this allows the dimension to grow, which is the only notion available for infinite Kazhdan groups by Becker--Lubotzky, and needs only finite generation
  sofic-stable-implies-residually-finite: that is the permutation principle for stability in finite actions; this is the unitary principle, closed by Malcev's theorem rather than by a finite action
---

**ESTABLISHED.** Let `Γ` be finitely generated and hyperlinear. Suppose `Γ` is
flexibly Hilbert--Schmidt stable: for every asymptotic representation
`π_n: Γ -> U(d_n)` there are genuine representations `ρ_n: Γ -> U(D_n)`,
`D_n >= d_n`, with `||π_n(g) - P_n ρ_n(g) P_n||_2 -> 0` for every `g`. Here `P_n`
projects onto the first `d_n` coordinates and `||·||_2` is normalized by `d_n`.
Then `Γ` is maximally almost periodic, hence residually finite.

Only the flexible notion is available for infinite hyperlinear Kazhdan groups:
Becker--Lubotzky exclude strict stability there. So this is the form of the
principle that stability routes into Kazhdan groups must use.

DERIVATION
hyperlinear-flexibly-hs-stable-group-is-residually-finite-proof
