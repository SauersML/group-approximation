---
rg: 2
id: deligne-stable-triple-cover-is-not-hyperlinear
kind: claim
title: For some genus g, Deligne's triple cover of Sp_2g(Z) is not hyperlinear
artifacts:
  - research/artifacts/deligne-hs-metric-ladder-2026-09-13.md
distinct_from:
  deligne-central-mark-hs-collapse: that is the one-word normalized-HS collapse at genus two, the strongest instance; this is the weakest triple-cover instance, over all genera, where more cohomology vanishing and the Frobenius collapse are available.
  dogon-sp2g-weak-ucp-nonhyperlinear: that makes the infinite cyclic universal-cover lattice non-hyperlinear under a stability hypothesis; this is the unconditional target for the finite triple covers, and non-hyperlinearity of a triple cover already forces non-hyperlinearity of the universal-cover lattice.
---

**OPEN.** There is `g >= 2` such that `E_3^(g)`, the preimage of `Sp_(2g)(Z)` in the connected
triple cover of `Sp_(2g)(R)`, is not hyperlinear.

**Equivalent forms.** By `deligne-cover-hyperlinearity-is-monotone-in-genus`, this holds iff it holds
for all large `g`, iff the countable direct limit `E_3^(infinity)` is not hyperlinear. At each genus
it amounts to three things:
- positive normalized-HS density of the nontrivial covering sector is impossible;
- the mod-three Maslov sector of `Sp_(2g)(Z)` has a dimension-free normalized defect gap;
- `1/3` is not a Connes-embeddable twist of `Sp_(2g)(Z)`.

The genus-two proofs (`deligne-sector-gap-equivalence-proof` and
`maslov-ce-closed-subgroup-proof`) use only a normalized integral covering cocycle, residual finiteness
of the base and finite-central sector cutting. They apply verbatim at every genus. This is recorded
as commentary, not as separate nodes.

**Payoff.** `E_3^(g)` is finitely presented, so this gives `non-hyperlinear-group`.

## Attempts

- **Genus two suffices.** `(DCM1)` at `g = 2` gives this claim by monotonicity
  (`deligne-stable-triple-cover-via-genus-two-collapse`). The converse direction is what makes the
  present claim weaker.
- **Unnormalized collapse: done at g >= 3.** By
  `deligne-symplectic-covers-are-not-schatten-approximated`, every Schatten-p asymptotic homomorphism
  with `p <= 2` kills `z`. Every nontrivial sector tuple in `U(d)` has normalized relator defect at
  least `delta d^(-1/2)`. The open core is exponent `0` instead of `1/2`.
  - A hyperlinear microstate must therefore spread its defect over full rank: its Frobenius defect
    `eta d^(1/2)` has to stay above `delta`.
  - The DGLT correction scheme behind the stability theorem cannot follow it there. The correction
    solving the linearized cocycle equation is small in normalized HS but has no operator-norm bound,
    and the quadratic error term needs one.
  - **Intermediate exponent (2026-09-13, ex2-nh-deligne-sector-floor).** Any exponent `b < 1/2` is
    open as `deligne-cover-sector-floor-below-exponent-one-half`, and bounded-rank defects are an
    even weaker open rung there. Monomial models over exact finite quotients have the floor `4 nu / A_0`
    at every genus (`deligne-monomial-cover-models-have-a-detecting-cycle-floor`), where `A_0` is the
    least mass of a detecting 2-cycle.
- **Two-norm arguments die at the normalized norm.** Bachner--Dogon--Lubotzky
  (`bdl-deligne-type-two-norm-inapproximability`) round the mark to an exact root of unity. A
  nontrivial root then costs a whole eigenvalue. In normalized HS one eigenvalue costs only
  `d^(-1/2)`, so the argument needs a positive fraction of the spectrum forced away from `1`. That
  forcing is this claim.
- **Operator norm, conditional, g >= 3.** `Gamma~_g` has `[T_2]` (BLSW Theorem 2.10), so BDL
  Conjecture 1.8 for it is the open `sp2g-universal-cover-lattice-is-operator-hs-stable`.
  - The route `deligne-sp2g-covers-not-mf-from-operator-hs-stability` derives that every `E_n^(g)`,
    `n >= 3`, has MF radical `<z^2>` and is not MF. It uses one application of the hypothesis to the
    compressed model, and it replaces the three-step sketch in Section 5 of the artifact.
  - That is weaker than this claim.
  - The covers themselves fail `[T_2]`, so the conjecture cannot be applied to them directly.
- **Flexible stability of the base (Dogon).** Flexible HS stability of `Sp_(2g)(Z)` would make
  `Gamma~_g` non-hyperlinear. `rf-kazhdan-group-not-flexibly-hs-stable` refutes flexible stability for
  `Z^(2g) x| Sp_(2g)(Z)` using exact projective twists tending to `1`.
  - That engine does not transfer to `Sp_(2g)(Z)`. An exact finite-dimensional projective
    representation with multiplier `exp(2 pi i t b_g)` is a representation of `Gamma~_g` with
    `z -> e^(2 pi i t)`.
  - Malcev and the finite residual `<z^2>` force `t in (1/2)Z` (at `g = 2` compare
    `sp4-fd-projective-multiplier-is-finite`).
  - The only replacement is approximate twists tending to `1`, which is hyperlinearity of `Gamma~_g`.
- **Stable twist order.** The sets `E_CE^(g)` shrink with `g` (monotonicity item 4). Each is a closed
  subgroup containing `1/2` (commentary above), so each is `R/Z` or `(1/M_g)Z/Z` with `M_g` even. A
  decreasing chain of such groups stabilizes at some `(1/M_infinity)Z/Z` or at `R/Z`. This claim says
  `3` does not divide `M_infinity` (or the chain is finite at all).
- **What does not help.** Exact finite quotients, fixed-representation Følner compressions and bounded
  block packets are excluded at every genus by the genus-two arguments, which are genus-independent.
  So is character rigidity alone. Dogon--Glasner--Gorfine--Hanany--Levit Theorem 1.5 applies to the
  triple cover of `Sp_(2g)(R)`, a connected semisimple group with finite center. It fixes the sector
  trace as central-regular but supplies no gap.
