---
rg: 2
id: thompson-f-cardinality-certificates-need-tower-degree
kind: claim
title: Cardinality certificates for Guba's Problems P_(d,m) in Thompson's F need degree growing faster than every fixed tower in log d
distinct_from:
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that makes non-amenability equivalent to doubling of some monomial set; this bounds from below the degree at which a non-doubling set can first be certified, for every (d,m).
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that computes the doubling ratio exactly in each fixed degree; this proves, unconditionally, that the first degree with ratio below 2 is huge once d is large.
  thompson-f-folner-function-exceeds-every-tower: that is Moore's lower bound on Følner sets for fixed generators; this transfers it to cardinality certificates for the homogeneous monomial sets of Guba's survey.
  thompson-f-p21-cardinality-certificate-in-degree-eleven: that exhibits one certificate for d = 2, m = 1; this is a lower bound that says nothing for d = 2 and forces huge degrees for large d.
artifacts:
  - research/artifacts/hl-thompson-f-2026-09-13.md
---

**ESTABLISHED** through `thompson-f-cardinality-certificates-need-tower-degree-proof` (direct proof from
Moore's theorem and two claims on main; not independently reviewed; no priority claimed).

Let `M` be the positive monoid of `F`, `M_D` its normal forms of degree `D`, and
`S = S_(m+1,m+d+1)` Guba's set of normal forms `x_(i_1) ... x_(i_d)` with `i_t <= m + t - 1`
(notation of `thompson-f-nonamenable-iff-some-monomial-set-doubles`). Let `C > 1` be the constant of
Moore's theorem (`thompson-f-folner-function-exceeds-every-tower`) for `Γ = {x_0^±1, x_1^±1}`, and
`exp_0(n) = n`, `exp_(p+1)(n) = 2^(exp_p(n))`.

**Theorem.** Let `m >= 1` and `d >= 2`. If some finite nonempty `Y ⊆ M_D` satisfies `|S Y| < 2|Y|`,
then

`exp_n(0) <= 2^(2D + m + 3d)` for every integer `n >= 0` with `C^n <= (d - 1)/8`.

Equivalently, with `n = ⌊log_C((d-1)/8)⌋ >= 1`: `D >= (exp_(n-1)(0) - m - 3d) / 2`.

**Consequences.**
- Let `D(d,m)` be the least degree carrying a cardinality certificate for `P_(d,m)` (item 3 of
  `thompson-f-nonamenable-iff-some-monomial-set-doubles`). As `d -> ∞`, `D(d,m)` eventually exceeds
  `exp_k(d)` for every fixed `k`, uniformly in `m <= d`.
- If `F` is amenable, item 1 of that claim makes every `D(d,m)` finite. So the cardinality method, which
  is exactly as strong as amenability, must use certificates of tower size in `log d` degrees.
- The same bound holds for any finite homogeneous `S' ⊆ M` containing `X_m X_(m+1) ... X_(m+d-1)`,
  where `X_k = {x_0, ..., x_k}`.

**Scope.**
- Moore's constant `C` is not explicit, so this gives no number for any specific `d`.
- Nothing follows for `d = 2`, in particular for `P_(2,2)`. There the exact values of
  `thompson-f-monomial-doubling-ratio-is-a-finite-computation` are the available information.
- Only the cardinality method is bounded. Solutions `a u = b v` found by linear algebra need no
  expansion and are not constrained by this argument (see
  `thompson-f-p22-explicit-pair-no-common-multiple-below-degree-9` and the artifact, where they appear in
  lower degrees than cardinality certificates).
