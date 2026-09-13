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
- **Decision audit, g = 2 (2026-09-13, lane `solve-nh-flexible-sp4`).**
  Undecided; the open core above is unchanged, and three candidate
  mechanisms are now closed or pinned.
  - **Literature, read from the TeX sources on MSI.**
    - Dogon arXiv:2211.10492, Definition 1.2 matches the statement here.
      p. 3 says "deciding flexible HS-stability in this scenario is
      extremely interesting", but it is not a numbered question.
    - Fournier-Facio--Gerasimova--Spaas arXiv:2307.13155, introduction:
      "Whereas flexible stability of most property (T) groups is open".
      Their theorem (infinite hyperlinear Kazhdan groups are never locally
      HS-stable) is, for finitely presented groups, the strict notion
      (their lemma that local and ordinary stability agree for finitely
      presented groups), so it does not touch this claim.
    - Becker--Lubotzky arXiv:1809.00632 §4.4 introduces the flexible notion
      as "a path towards finding a non-sofic group" (permutation version).
  - **The hyperfinite part is already known.**
    `character-rigidity-equals-hyperfinite-hs-stability` (Dogon--Vigdorovich
    Theorem 1.6) makes hyperfinite HS-stability equivalent to character
    rigidity for irreducible lattices with (T;FD) in center-free higher-rank
    groups. Their introduction records character rigidity "most notably when
    G has a property (T) factor", citing Bekka, Peterson and others. Those
    were not re-read here.
    - So `PSp_4(Z) <= PSp_4(R)` is hyperfinitely HS-stable.
    - Any non-roundable asymptotic representation of `PSp_4(Z)` therefore has
      a non-hyperfinite limit.
    - Passing between `Sp_4(Z)` and `PSp_4(Z)` is not claimed.
  - **Scalar-cocycle witnesses have no input.**
    `sp4-projective-models-with-cocycles-to-one-round-strictly`: every exact
    finite-dimensional projective model of `Sp_4(Z)` with cocycles tending
    to 1 rounds strictly in operator norm, because only finitely many classes
    are realized in finite dimensions (`sp4-fd-projective-multiplier-is-finite`).
    - This is the mechanism of `rf-kazhdan-group-not-flexibly-hs-stable`
      (the Ioana--Spaas--Wiersma Theorem A remark, Heisenberg covers), and it
      cannot refute this claim at g = 2.
    - A counterexample needs non-scalar defects, or asymptotically projective
      models at non-realized twists. A Connes-embeddable sequence of the
      latter refutes the claim (twisted-sector bullet above).
  - **Kazhdan covers, product case (hand remark).**
    `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` says models
    pulled back from a Kazhdan cover round iff the kernel's fixed mass tends
    to 1. Product covers `Sp_4(Z) x K`, with `K` Kazhdan and Kazhdan pair
    `(Q,κ)`, give nothing.
    - For a unitary `τ : K -> U(d)` with fixed projection `E`, every
      `v ⊥ ran E` has `Σ_(q∈Q) ||(τ(q)-1)v||^2 >= κ^2 ||v||^2`.
    - Summing over an orthonormal basis of `ran(1-E)` gives
      `Σ_q ||τ(q)-1||_(2,d)^2 >= κ^2 tr_d(1-E)`.
    - So condition (KC1) forces `tr_d E -> 1`.
    - A counterexample from that criterion needs a finitely presented Kazhdan
      cover whose kernel is elementwise almost trivial but has common fixed
      mass bounded away from 1. None is known.
- **Correctors factor through finite quotients (2026-09-13, lane
  `solve-nh-flexible-nonscalar`).**  New claim
  `sp4-flexible-correctors-factor-through-finite-quotients` (route
  `sp4-flexible-correctors-finite-quotient-proof`), resting on the new
  `sp4-fd-unitary-reps-have-finite-image` (Margulis superrigidity, compact
  target: every finite-dimensional unitary representation of `Sp_(2g)(Z)`,
  `g >= 2`, has finite image).
  - Any flexible correction of an asymptotic homomorphism uses genuine
    finite-dimensional unitary `pi_n`, so each `pi_n` factors through a
    finite quotient, and by Bass--Milnor--Serre through a congruence
    quotient `Sp_(2g)(Z/N_n)`.
  - So flexible HS-stability of `Gamma` is EQUIVALENT to flexible
    congruence-quotient approximability of asymptotic homomorphisms.
  - A scalar twisted-sector refutation must use `[c_n]` pulled back from a
    finite Schur multiplier `H^2(Sp_(2g)(Z/N),T)`; the infinite-order
    Deligne class does not descend to any finite quotient
    (`deligne-universal-cover-lattice-is-non-rf-kazhdan`), so it is
    invisible to the correctors.  This re-explains the finiteness of
    `sp4-fd-projective-multiplier-is-finite` (finite quotients have finite
    Schur multipliers).
  - **Sharpened open core.**  With
    `character-rigidity-equals-hyperfinite-hs-stability` giving the limit
    trace as a finite-quotient character limit, the residual obstruction is
    not the trace but matching `phi_n` to a congruence-quotient
    representation at dimension ratio `-> 1`: a lim^1 / Ext-type
    dimension-ratio obstruction concentrated on the Deligne `Z`-direction.
    No refutation found; the claim stays OPEN.
