---
rg: 2
id: sp2g-z-full-c-star-algebra-has-llp
kind: claim
title: The full C*-algebra of some symplectic lattice Sp_2g(Z) has the local lifting property
distinct_from:
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that asks for LLP for a NON-residually-finite Kazhdan group, whose existence is itself part of the question; this asks it for the concrete residually finite lattices Sp_2g(Z), where the group is classical and only the lifting property is unknown.
  sl3-z-weakly-ucp-stable: that is a stability hypothesis for SL_3(Z), attacked as a rigidity statement about almost-representations; this is a lifting hypothesis for Sp_2g(Z), attacked (either way) by C*-tensor methods, and it IMPLIES the corresponding weak ucp-stability of Sp_2g(Z) by llp-implies-weak-ucp-stability.
---

OPEN CLAIM.  For some `g >= 2`, the full group C*-algebra
`C^*(Sp_(2g)(Z))` has Kirchberg's local lifting property.

By `llp-implies-weak-ucp-stability` and `dogon-sp2g-weak-ucp-nonhyperlinear`
this makes Deligne's universal-cover lattice non-hyperlinear
(`non-hyperlinear-from-sp2g-llp`).  The negation is equally quotable: with
Ioana--Spaas--Wiersma's `SL_n(Z)` results it would say every classical
higher-rank arithmetic lattice fails LLP, answering the question
Fournier-Facio--Willett record: "It seems to be open whether higher rank
arithmetic groups always fail the (L)LP" (arXiv:2603.18456v2, p. 7,
discussion after Question 1.10; source-verified 2026-08-21).

## Attempts

- **Fences.**  Ioana--Spaas--Wiersma (arXiv:2006.01874): `C^*(SL_n(Z))`
  fails LLP for `n >= 3`, and `C^*(Z^2 rtimes F_2)` (standard action,
  `F_2 <= SL_2(Z)` finite index) fails LLP.  LLP passes to subgroups
  (Fournier-Facio--Willett Cor. 3.17), so a positive answer requires that
  `Sp_(2g)(Z)` contain no subgroup of the fenced kinds.  `Sp_(2g)(Z)`
  contains no `SL_3(Z)` acting through a 3-dimensional symplectic...
  no: it does contain `SL_g(Z)` (Siegel Levi) for `g >= 3`, which KILLS
  the claim for `g >= 3` by subgroup permanence.  The claim therefore
  lives at `g = 2` ONLY: `Sp_4(Z)`, whose Siegel Levi is `GL_2(Z)`
  (virtually free, LLP-safe) and whose Klingen unipotent radical is the
  integer Heisenberg group (amenable, LLP-safe).  The open content is
  whether the Ioana--Spaas--Wiersma cohomological obstruction extends
  from the standard pair `(Z^2, SL_2(Z))` to the pairs inside `Sp_4(Z)`:
  the Siegel pair `(Sym^2(Z^2), GL_2(Z))` and the Klingen pair
  (Heisenberg by `SL_2(Z)`), both with relative property (T).  If it
  does, `Sp_4(Z)` fails LLP too and the higher-rank question closes
  negatively; no such extension is published.
- **Why a positive answer is not absurd.**  The known LLP failures all
  pass through second cohomology of relative-(T) pairs with COEFFICIENTS
  where the standard pair has its obstruction class; `Sp_4(Z)` is the
  classical case where the relevant `H^2` is carried by the Deligne
  class, which is a BOUNDED class with finite-image restriction to every
  congruence subgroup's... this is exactly the arithmetic the direct
  Deligne lane (`deligne-central-mark-hs-collapse`) manipulates.  No
  computation in either direction is recorded; this node parks the
  question in its sharpest form (`g = 2`).
- **Method note.**  Any attack should start from Ioana--Spaas--Wiersma's
  actual mechanism (their Theorem A/Corollary B derivation) rather than
  from tensor-norm generalities: the Kirchberg characterization
  `LLP <=> (x)_max B(l^2) = (x)_min B(l^2)` has never been verified or
  refuted directly for any lattice.
