---
rg: 2
id: quasitrace-iff-not-stably-properly-infinite
kind: claim
title: A unital C*-algebra admits a normalized 2-quasitrace iff no matrix algebra over it is properly infinite
distinct_from:
  normalized-quasitraces-detected-finitely: that is a compactness statement localizing the absence of quasitraces to a finitely generated subalgebra; this is the existence criterion itself, in terms of proper infiniteness of matrix algebras.
artifacts:
  - research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md
---

**ESTABLISHED (literature).**  A unital C\*-algebra `A` admits a normalized
2-quasitrace if and only if `M_n(A)` is properly infinite for no `n >= 1`, that
is, iff `A` is not stably properly infinite.

This is Theorem 2.3 of Milhøj–Rørdam, *Around traces and quasitraces*,
arXiv:2309.17412v2, attributed to Cuntz and Blackadar–Handelman.  The "only if"
direction holds because a properly infinite algebra admits no quasitrace and
quasitraces extend to matrix algebras.  For the "if" direction, the positive
map `N_0<1> -> R`, `n<1> -> n`, extends to a state on the Cuntz semigroup
normalized at the unit (Blackadar–Rørdam).  Its lower semicontinuous
regularization is a normalized lower semicontinuous dimension function, and it
extends to a 2-quasitrace (Blackadar–Handelman Theorem II.2.2).

For simple algebras "not stably properly infinite" and "stably finite"
coincide, by Cuntz's observation that infinite projections in simple
C\*-algebras are properly infinite.
