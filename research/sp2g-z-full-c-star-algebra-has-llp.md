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
  `Sp_(2g)(Z)` contain no subgroup of the fenced kinds.  For `g >= 3`
  the Siegel Levi `GL_g(Z) <= Sp_(2g)(Z)` contains `SL_g(Z)`, which fails
  LLP, so subgroup permanence refutes the claim for `g >= 3` outright.
  The claim therefore lives at `g = 2` only: `Sp_4(Z)`, whose Siegel Levi is `GL_2(Z)`
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
  classical case where the relevant second cohomology is carried by the
  Deligne/Maslov class — exactly the arithmetic that the direct Deligne
  lane (`deligne-central-mark-hs-collapse`) manipulates — and no
  published computation locates an Ioana--Spaas--Wiersma-type
  obstruction class for the Siegel or Klingen pairs of `Sp_4(Z)`.  No
  computation in either direction is recorded; this node parks the
  question in its sharpest form (`g = 2`).
- **LP already fails, so this hole would separate LLP from LP.**
  Ioana--Spaas--Wiersma Example 1.3(i) (read at source 2026-08-21):
  `H^2(Sp_(2n)(Z), R) != 0` for `n >= 2`, so by their Corollary E
  `C^*(Sp_(2n)(Z))` fails the (global) LP.  Hence a positive answer here
  would exhibit a separable C*-algebra with LLP but not LP — an open
  problem of Ozawa they cite — on top of the non-hyperlinear group.  Both
  prizes at once argues for pessimism, but the refutation side is now
  also fenced: `sp4-metaplectic-class-pointwise-coboundary-limit` (with
  its compactness proof) shows a FIXED nontrivial scalar class is never a
  pointwise limit of coboundaries, so the Ioana--Spaas--Wiersma Theorem A
  attack needs infinitely many DISTINCT finite-dimensionally realized
  classes tending to the trivial class, nontrivial on a relative-(T)
  subgroup; on the Deligne circle only the trivial and metaplectic
  classes are realizable (Deligne invisibility), and the odd-level Weil
  representations are genuine representations, whose classes are
  coboundaries.  No candidate family for the ISW mechanism at `Sp_4(Z)`
  is recorded, so BOTH directions of this hole now require a new idea.
- **Method note.**  Any attack should start from Ioana--Spaas--Wiersma's
  actual mechanism (their Theorem A/Corollary B derivation) rather than
  from tensor-norm generalities: the Kirchberg characterization
  `LLP <=> (x)_max B(l^2) = (x)_min B(l^2)` has never been verified or
  refuted directly for any lattice.

## Parabolic audit

The two immediate ways of importing the known obstruction are now closed.
`sp4-maximal-parabolics-contain-no-isw-affine-subgroup` proves that neither
the Siegel nor Klingen parabolic contains the standard
`Z^2 rtimes F_2` obstruction group.  More strongly,
`isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals` computes
that the Levi-invariant scalar `H^2` of either radical is finite.  Hence no
pointwise-trivial sequence can remain nontrivial on the relative-`(T)`
radical, so ISW Theorem A itself cannot be rerun there.  The remaining
possibilities are a genuinely global affine subgroup of `Sp_4(Z)`, or the
operator-valued mechanism of ISW Theorem C with new coefficient and
embeddability input.

The other proposed scalar shortcut is closed universally:
`sp4-metaplectic-class-pointwise-coboundary-limit` proves that
`B^2(Gamma,T)` is pointwise closed for every discrete group.  Hence a fixed
metaplectic class cannot supply the pointwise-trivial sequence in ISW
Theorem A merely by changing representatives.
