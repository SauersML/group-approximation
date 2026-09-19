---
rg: 2
id: kun-thom-hyperfinite-character-firewall-proof
kind: route
title: Apply the amenable-character criterion, then test the exact-base shortcut on the orbit chain
target: kt-polynomial-hyperfinite-stability-misses-regular-wreath
requires:
  - one-compressor-covariance-has-free-hs-telescope
  - kazhdan-polar-rounding-produces-supported-gallery-edges
---

Dogon--Vigdorovich, arXiv:2506.20843v2, Theorem 6.2, states for an
arbitrary finitely generated group that hyperfinite HS stability is
equivalent to approximation of every von Neumann amenable character by
normalized traces of finite-dimensional representations.

Let `chi` be an extremal von Neumann amenable character of
`Gamma=EL_r(R)` in the stable range `(KHF1)`.  Lavi--Levit, Corollary 1.3 of
arXiv:2007.15547, writes `chi` as induction from a finite-dimensional
representation of a normal subgroup `N`, with `chi=0` off `N`.  The product
`chi conjugate(chi)` dominates a positive multiple of the quotient character
`1_N`.  Amenability passes to the dominated GNS corner, so `L(Gamma/N)` is
amenable.  Hence `Gamma/N` is amenable.  Property `(T)` passes to this
quotient, and an amenable discrete property-`(T)` group is finite.  Therefore
`N` has finite index and the induced representation is finite dimensional.
Every amenable extremal character, and then every amenable character by
ergodic decomposition, is approximable by finite-dimensional traces.
Dogon--Vigdorovich gives hyperfinite HS stability.

For a canonical trace microstate, restriction to `Gamma` converges to
`delta_e`; its GNS algebra is `L(Gamma)`.  Since `Gamma` is infinite with
property `(T)`, it is nonamenable, and the standard equivalence
`L(Gamma) amenable iff Gamma amenable` excludes the hyperfinite hypothesis.

Finally apply the exact orbit-chain construction of
`one-compressor-covariance-has-free-hs-telescope` to the polynomial shear.
The base is genuine at every stage and the covariance defect is
`2/sqrt(L)`.  The finite quotient tower from the polynomial-shear
macroscopic-strictness theorem supplies `(KHF6)`.  Kazhdan polar rounding
returns exactly the non-wrapping partial shift, with endpoint loss `(KHF7)`;
it does not turn it into a common-carrier unitary.  Hence the same models
refute the exact-base-only inference `(KHF8)` while remaining fully
consistent with hyperfinite HS stability.
