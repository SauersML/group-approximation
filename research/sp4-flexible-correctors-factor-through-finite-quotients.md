---
rg: 2
id: sp4-flexible-correctors-factor-through-finite-quotients
kind: claim
title: In any flexible HS-stability witness for Sp_2g(Z), the correcting representations factor through finite (congruence) quotients
distinct_from:
  sp2g-z-flexibly-hs-stable: that is the open stability claim itself; this is a structural constraint on ANY witness for it, valid whether or not stability holds.
  character-rigidity-equals-hyperfinite-hs-stability: that concerns the TRACE of the limit (the hyperfinite part); this concerns the finite-dimensional correctors and isolates the residual obstruction to the dimension ratio and the Deligne direction.
  sp4-fd-projective-multiplier-is-finite: that bounds realizable scalar classes; this locates where a twisted-sector refutation must live (Schur multipliers of finite congruence quotients) and why the Deligne class is invisible to correctors.
---

**CLAIM (ESTABLISHED, not independently reviewed).**  Let
`Gamma = Sp_(2g)(Z)`, `g >= 2`.  Suppose `phi_n : Gamma -> U(d_n)` is an
asymptotic homomorphism admitting a flexible correction: genuine
representations `pi_n : Gamma -> U(D_n)`, `D_n >= d_n`, `D_n / d_n -> 1`,
with `|| phi_n(x) - P_n pi_n(x) P_n ||_(2, tau_(d_n)) -> 0` for all `x`
(`P_n` the corner projection).  Then:

1. **(FQ1)**  Each `pi_n` factors through a finite quotient of `Gamma`.  By
   the Bass--Milnor--Serre congruence subgroup property for `Sp_(2g)(Z)`,
   `g >= 2` (cited at statement level), that quotient is a quotient of a
   principal congruence quotient `Sp_(2g)(Z / N_n)`.
2. **(FQ2)**  Consequently flexible HS-stability of `Gamma` is EQUIVALENT to
   the statement that every asymptotic homomorphism is flexibly
   `2`-norm-approximated (dimension ratio `-> 1`) by representations of the
   finite congruence quotients `Sp_(2g)(Z / N)`.
3. **(FQ3)**  A scalar twisted-sector refutation (a Connes-embeddable
   sequence of almost-trivial nontrivial twisted algebras `L_(c_n)(Gamma)`,
   the mechanism recorded in `sp2g-z-flexibly-hs-stable`) must use classes
   `[c_n]` pulled back from the Schur multipliers `H^2(Sp_(2g)(Z/N), T)` of
   finite congruence quotients, all of which are finite groups.  In
   particular the infinite-order Deligne class in `H^2(Gamma, Z)` coming
   from `pi_1(Sp_(2g)(R)) = Z` does NOT descend to any finite quotient --
   that non-descent is exactly the non-residual-finiteness of the Deligne
   cover, `deligne-universal-cover-lattice-is-non-rf-kazhdan` -- so it is
   invisible to the correctors.

## Consequence for the open core

Combined with `character-rigidity-equals-hyperfinite-hs-stability` (the
limit trace of any asymptotic homomorphism of `PSp_(2g)(Z)` is a
finite-quotient character limit), (FQ2) shows the residual obstruction to
flexible stability is NOT about which trace the limit carries, but about
matching `phi_n` to a congruence-quotient representation with dimension
ratio `-> 1`.  This sharpens the node's standing "correction theorem for
non-hyperfinite asymptotic representations" to: a lim^1 / Ext-type
dimension-ratio obstruction concentrated on the Deligne `Z`-direction, the
one direction finite quotients cannot see.

## Proof

Route `sp4-flexible-correctors-finite-quotient-proof`, requiring
`sp4-fd-unitary-reps-have-finite-image`.

## Trust surface

- `sp4-fd-unitary-reps-have-finite-image` (established here; itself cites
  Margulis superrigidity at statement level).
- Bass--Milnor--Serre congruence subgroup property for `Sp_(2g)(Z)`,
  `g >= 2`, cited at statement level for the refinement "finite quotient =
  congruence quotient" in (FQ1) and (FQ2).  The core reduction (correctors
  factor through SOME finite quotient) needs only finite image, not CSP.
- The non-descent of the Deligne class is `deligne-universal-cover-lattice-
  is-non-rf-kazhdan`.

No novelty is claimed for the superrigidity or CSP inputs; the new content
is the reduction (FQ1)--(FQ3) and the localisation of the obstruction.
