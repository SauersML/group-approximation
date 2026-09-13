---
rg: 2
id: sp4-fd-unitary-reps-have-finite-image
kind: claim
title: Every finite-dimensional unitary representation of Sp_2g(Z), g >= 2, has finite image
distinct_from:
  sp4-fd-projective-multiplier-is-finite: that bounds the SCALAR classes in H^2(Gamma,T) realized by finite-dimensional PROJECTIVE representations; this is about genuine (linear) finite-dimensional UNITARY representations and concludes their image is finite.
  character-rigidity-equals-hyperfinite-hs-stability: that classifies TRACES on the group von Neumann algebra via character rigidity; this is an elementary superrigidity fact about honest finite-dimensional unitary representations, used as its input downstream.
---

**CLAIM (ESTABLISHED).**  Let `Gamma = Sp_(2g)(Z)` with `g >= 2` and let
`rho : Gamma -> U(k)` be a finite-dimensional unitary representation
(`k < infinity`).  Then `rho(Gamma)` is finite; equivalently `ker rho` has
finite index, so `rho` factors through a finite quotient of `Gamma`.

This is special to the higher-rank arithmetic lattice.  Free groups, surface
groups and `SL_2(Z)` all carry finite-dimensional unitary representations
with infinite image; the statement fails for them.

## Why it matters

It is the structural input for
`sp4-flexible-correctors-factor-through-finite-quotients`: in any flexible
Hilbert--Schmidt stability witness for `Gamma`, the correcting genuine
representations are finite-dimensional and unitary, hence by this claim they
factor through finite quotients.  It also re-explains, conceptually, the
finiteness in `sp4-fd-projective-multiplier-is-finite`: a finite quotient has
a finite Schur multiplier, so only finitely many scalar classes can be seen
in finite dimensions.

## Proof

Route `sp4-fd-unitary-reps-finite-image-via-superrigidity`.  In outline:

1. `rho(Gamma) <= U(k)` is contained in a compact group.
2. **Margulis superrigidity, compact case** (cited at statement level; see
   the Trust surface).  For an irreducible lattice `Gamma` in a connected
   semisimple Lie group `G` of real rank `>= 2` with trivial centre and no
   compact factors, and `rho : Gamma -> K` a homomorphism into a compact
   real Lie group, either `rho(Gamma)` is finite or, on a finite-index
   subgroup, `rho` extends to a continuous homomorphism `G -> K`.  Here
   `G = Sp_(2g)(R)`, which is connected, simple and of real rank `g >= 2`,
   and `Gamma = Sp_(2g)(Z)` is an irreducible lattice.
3. **No nontrivial continuous homomorphism `Sp_(2g)(R) -> K` into a compact
   group** (elementary, self-contained).  Such a homomorphism has
   differential a Lie-algebra homomorphism `sp(2g,R) -> k`.  Since
   `sp(2g,R)` is simple, the differential is either zero or injective.  A
   compact Lie algebra `k` has negative semidefinite Killing form, so every
   subalgebra of it does too; but `sp(2g,R)` is a real simple Lie algebra of
   non-compact type, whose Killing form is indefinite.  Hence there is no
   injective Lie-algebra homomorphism `sp(2g,R) -> k`, the differential is
   zero, and the homomorphism is trivial on the identity component, hence
   trivial (`Sp_(2g)(R)` is connected).
4. So the extension in (2) is trivial, forcing `rho(Gamma)` finite.

## Trust surface

- **Margulis superrigidity (compact target).**  Cited at the level of its
  statement, not re-read this session.  Standard references: Margulis,
  *Discrete Subgroups of Semisimple Lie Groups*, Chapter VII; Zimmer,
  *Ergodic Theory and Semisimple Groups*, superrigidity for compact targets.
  The repository already relies on Margulis's normal subgroup theorem for
  `Sp_(2g)(Z)` (see `sp2g-z-flexibly-hs-stable`, "No permanence shortcuts");
  this uses the companion superrigidity theorem at the same level.
- Everything else (steps 1, 3, 4) is elementary and self-contained.

No novelty is claimed: this is a textbook consequence of superrigidity.  The
node records it because no existing node states it and two downstream nodes
need it.
