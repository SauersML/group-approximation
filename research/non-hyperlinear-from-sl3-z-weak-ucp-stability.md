---
rg: 2
id: non-hyperlinear-from-sl3-z-weak-ucp-stability
kind: route
title: Weak ucp-stability of SL_3(Z) is flexible stability on its microstates, so the thin co-dense HNN extension is non-hyperlinear
target: non-hyperlinear-group
requires:
  - sl3-z-weakly-ucp-stable
  - kazhdan-weak-ucp-stability-is-flexible-stability
  - sln-z-thin-codense-tau-pair
  - hnn-over-codense-kazhdan-subgroup-not-hyperlinear
---

Take `A = SL_3(Z)` with the thin co-dense `(tau)` subgroup `C` of
`sln-z-thin-codense-tau-pair` (explicitly, the two displayed integer
matrices `a, b` of `explicit-sl3-thin-codense-tau-pair`, so that the
endpoint is the literal finitely presented group
`G = < SL_3(Z), t | [t, a] = 1, [t, b] = 1 >` with marked word `[t, r]`).

Suppose `G` were hyperlinear, with hyperlinear approximation
`phi_n : G -> U(d_n)`.  The restriction `phi_n|_A` is a hyperlinear
approximation of `A = SL_3(Z)` (asymptotic multiplicativity and the
separation `liminf || phi_n(a) - 1 ||_2 >= sqrt 2`, `a != e`, are inherited
from `G`).  By `sl3-z-weakly-ucp-stable` it is pointwise asymptotic to
corners of genuine representations on possibly infinite-dimensional
dilation spaces; since `SL_3(Z)` has property (T),
`kazhdan-weak-ucp-stability-is-flexible-stability` upgrades these to genuine
FINITE-dimensional representations `rho_n` of `A` on `C^(D_n) supseteq
C^(d_n)`, `D_n / d_n -> 1`, with `|| phi_n(a) - P_n rho_n(a) P_n ||_2 -> 0`.

This is precisely the input that the proof of
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` consumes: it applies
flexible HS-stability of the host ONLY to the microstate sequence of the
HNN group restricted to the host (artifact
`research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md` §11,
"if a tuple of defect `tau` has `A`-part within `eta` of an exact `rho`
... flexible HS-stability of `A` (padding by the identity on the extra
corner) gives `eta -> 0`").  With the `(tau)` gap of `C` on the congruence
quotients through which every finite-dimensional representation of `A`
factors, and co-density `rho(C)' = rho(A)'`, the letter `U(t)` is pushed
onto the commutant of `rho_n(A)` and `tr phi_n([t, r]) -> 1`, while Britton
gives `[t, r] != e` and hyperlinearity of `G` demands `tr phi_n([t, r])
-> 0`.  Contradiction: `G` is not hyperlinear.

**Relation to `non-hyperlinear-from-hnn-over-sln-z`.**  That route requires
`sln-z-flexibly-hs-stable` -- flexible HS-stability of some `SL_n(Z)`,
`n >= 3`, for ALL asymptotic homomorphisms.  This route requires only the
`n = 3`, hyperlinear-approximation form, stated in Dogon's formally weaker
ucp language; by the lemma the two forms coincide for Kazhdan groups, so
the gain is exactly the quantifier restriction (separating sequences
only), which is all the HNN mechanism ever used.  It supersedes the
face-confinement consumption of `sl3-z-weakly-ucp-stable` through
`kazhdan-subgroup-weak-ucp-exactifies-microstates`, which needed the
`Lambda`-exact face closure in addition.
