---
rg: 2
id: sp2g-z-flexibly-hs-stable
kind: claim
title: Some symplectic lattice Sp_2g(Z) is flexibly Hilbert-Schmidt stable
distinct_from:
  sln-z-flexibly-hs-stable: that is flexible HS-stability of SL_n(Z), consumed through a thin co-dense HNN pair; this is flexible HS-stability of Sp_2g(Z), consumed through Deligne's universal-cover central extension by Dogon Corollary 1.9 with no auxiliary construction.
  sl3-z-weakly-ucp-stable: that is the n = 3 instance for SL_3(Z); this concerns the symplectic lattices, where pi_1(Sp_2g(R)) = Z supplies the central extension directly.
  sp2g-z-full-c-star-algebra-has-llp: that is a lifting hypothesis, implying weak ucp-stability and possible only at g = 2 by the Siegel-Levi fence; this is the stability hypothesis itself, not fenced at g >= 3 by LLP failure.
  kazhdan-hyperbolic-b2-group-flexibly-hs-stable: that asks flexible stability of a hyperbolic Kazhdan group with b_2 >= 1; this asks it of a higher-rank arithmetic lattice, which is not hyperbolic.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is the Becker--Lubotzky no-go for STRICT (same-dimension) stability; this is the FLEXIBLE notion, which that theorem leaves open.
---

OPEN CLAIM.  For some `g >= 2`, `Gamma = Sp_(2g)(Z)` is flexibly
Hilbert--Schmidt stable (Dogon arXiv:2211.10492v3 Definition 1.2, after
Becker--Lubotzky): every asymptotic homomorphism
`phi_n : Gamma -> U(d_n)` admits genuine representations
`pi_n : Gamma -> U(D_n)`, `D_n >= d_n`, `D_n/d_n -> 1`, with
`|| phi_n(g) - P_n pi_n(g) P_n ||_(2,tau_(d_n)) -> 0` for all `g`.

**Payoff.**  Flexible HS-stability implies weak ucp-stability (immediate
direction of `kazhdan-weak-ucp-stability-is-flexible-stability`), so by
`dogon-sp2g-weak-ucp-nonhyperlinear` (Dogon Corollary 1.9) the pullback
`Gamma~` of `Gamma` to the universal cover of `Sp_(2g)(R)`, Deligne's
non-residually-finite lattice, is not hyperlinear.  Route
`non-hyperlinear-from-sp2g-flexible-hs-stability`.

## Attempts

- **Becker--Lubotzky scope (arXiv:1809.00632v2, read from the PDF on
  2026-09-12).**  Theorem 1.3(ii): "If Gamma is hyperlinear and has
  Property T, then it is not HS-stable, unless it is finite."  Theorem
  1.4: a Kazhdan group that is P-stable or HS-stable "has only finitely
  many finite-index subgroups."  The proof counts finite quotients through
  SAME-dimension corrections.  Flexible correction (`D_n/d_n -> 1`) pads the
  dimension and the count no longer applies, so the theorem obstructs
  strict stability only (`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`).
  Dogon (p. 3): "there is no known example of a group that is flexibly
  HS-stable, but not HS-stable."  A proof here would be the first.
- **The weak-ucp wording is not easier.**  `Gamma` is hyperlinear and
  Kazhdan, so `kazhdan-weak-ucp-stability-is-flexible-stability` makes weak
  ucp-stability exactly full flexible stability.
- **Lifting routes.**  LLP of `C^*(Sp_(2g)(Z))` would suffice through
  `llp-implies-weak-ucp-stability`, but by the Siegel-Levi fence in
  `sp2g-z-full-c-star-algebra-has-llp` it is impossible for `g >= 3`, and
  the global LP fails for all `g >= 2` (Ioana--Spaas--Wiersma Example
  1.3(i)).  Failure of LP or LLP does not refute stability, so for `g >= 3`
  only a direct correction theorem remains.
- **Twisted-sector obstruction (proved).**
  `sp2g-flexible-stability-forces-twisted-non-ce`: stability forces every
  almost-trivial nontrivial twisted algebra `L_(c_n)(Gamma)` to be non
  Connes-embeddable eventually (Dogon Theorem 3.1, contrapositive).  So a
  single Connes embedding of such a sequence REFUTES this claim, and any
  proof must already contain non-Connes-embeddability of those twisted
  algebras, which by `effective-twisted-factor-existence-is-fp-nonhyperlinearity`
  is itself a finitely presented non-hyperlinear witness.  Stability is
  therefore not a smaller stepping stone than the goal on the twisted
  sector; it adds a correction statement on top of it.
- **No permanence shortcuts.**
  - Flexible stability does not pass to subgroups (virtually free groups
    are flexibly stable, `F_m x F_k` is not, Ioana).  So the non-stability
    of `SL_2(Z) x| Z^2` (Ioana--Spaas--Wiersma), a subgroup of `Sp_4(Z)`,
    does not transfer to `Sp_4(Z)` by inclusion.
  - By the Margulis normal subgroup theorem every normal subgroup of
    `Sp_(2g)(Z)`, `g >= 2`, is finite or of finite index, so
    `flexible-hs-stability-passes-to-kazhdan-kernel-quotients` yields only
    finite quotients.
- **What remains.**  A correction theorem for non-hyperfinite asymptotic
  representations of a higher-rank Kazhdan lattice against the (T)
  obstruction.  This is the same open core as `sln-z-flexibly-hs-stable`.
