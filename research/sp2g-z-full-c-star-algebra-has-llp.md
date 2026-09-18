---
rg: 2
id: sp2g-z-full-c-star-algebra-has-llp
kind: claim
title: The full C*-algebra of some symplectic lattice Sp_2g(Z) has the local lifting property
artifacts:
  - research/artifacts/lifting-program-2026-08-21.md
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

- **Decision audit (2026-09-13; artifact
  `research/artifacts/sp4-llp-decide-2026-09-13.md`).**  Neither side is
  decided, and each reduces to a well-known hard statement.
  - *Positive side.*  Block-diagonal `SL_2(Z) x SL_2(Z) <= Sp_4(Z)` contains
    `F_2 x F_2`.  So LLP here would answer the LLP halves of
    Fournier-Facio--Willett Questions 1.6 ("Does `F_2 x F_2` have the
    (L)LP?") and 1.9 (an infinite property (T) group with the (L)LP), both
    on arXiv:2603.18456v2 p. 6.  It would also make a finite Deligne cover
    nonhyperlinear (`sp4-llp-failure-or-maslov-nonhyperlinear-extension`).
  - *Refutation side.*  ISW Theorem 4.3 (arXiv:2006.01874, pp. 17-18) at
    `A = C1` needs exactly `sp4-small-maslov-twisted-group-factors-are-ce`.
    Theorem G and Corollaries D/E conclude only LP.  FF-W Corollary 3.36
    and Example 3.37 (pp. 24-25) move LLP upward, and the rank-one `H_2`
    blocks them.
  - `sp4-finite-index-scalar-data-iff-hyperlinear-covers` covers two kinds
    of packet: scalar packets on any finite-index subgroup, and packets over
    any finite transitive action.  Such packets exist iff some
    infinite-order integral class has every finite cyclic central cover
    hyperlinear.  Only finitely many of those covers are residually
    amenable.
  - Two refutation mouths remain.  One is hyperlinearity of
    non-residually-amenable Kazhdan central covers.  The other is a
    non-atomic action with non-constant cocycles; no candidate is known.
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
- **Literature gate and Klingen Theorem C reframing (2026-09-17, d-sp2g).**

  *Gate.*  No published theorem refutes the LLP for `Sp_4(Z)`.
  Ioana--Spaas--Wiersma (arXiv:2006.01874, e-print TeX line 341) prove
  only the LP failure: "Since $C^*(\text{SL}_3(\mathbb Z))$ and
  $C^*(\text{Sp}_4(\mathbb Z))$ do not have the \text{LP} by (i) and
  (ii)...".  Pisier (arXiv:2304.01667) writes: "It remains an open
  question whether all discrete groups with property (T) fail the LP
  or even the LLP."  The Kirchberg-type obstruction (LLP + (T) +
  hyperlinear gives residually finite) does not bite, because `Sp_4(Z)`
  is residually finite.  `g >= 3` stays refuted via `SL_3(Z)`.

  *Reframing.*  Rerun Theorem C on the Klingen subgroup
  `Gamma = H_omega x| Sigma`, not on `Sp_4(Z)`.  A success would refute
  this claim at `g = 2` by subgroup permanence.
  - New, ESTABLISHED: `klingen-heisenberg-pair-has-relative-property-t`,
    that `(H_omega x| Sigma, H_omega)` has relative (T).  NPSgen forces
    `z^2` to act trivially on almost invariant vectors, and Burger
    finishes.  This closes the "unchecked sketch" of the 09-16 note.
  - New, ESTABLISHED: `theorem-c-on-klingen-subgroups-needs-non-free-radical-action`.
    - The radical cannot act essentially freely (ISW line 287: `H^2 = 0`
      for free amenable actions).  So Bernoulli/Jiang supply is dead
      there.
    - When a power of the center acts trivially, the commutator
      1-cocycle `c(g,z^j)c(z^j,g)^*` is a coboundary by relative (T).
      So `c_n|Lambda` untwists to a class inflated from the virtually
      abelian `Lambda/<z^j>`.  This kills the solenoid / `T^2`
      `E^{1,1} = H^1(Z^2, L^0)` candidate.

  *Where it stops.*  Two supply cases remain, both OPEN:
  - (S1) classes inflated from `Lambda/N` outside the inflation kernel
    `T * e_N`;
  - (S2) the center acts freely, but the radical does not (stabilizers
    abelian).

  Connes embeddability of the twisted crossed products is expected to be
  easy here (amenable radical; the virtually free Levi untwists cocycle
  actions; amalgamated free products over an injective base).  That
  needs a verbatim Brown--Dykema--Jung import and is not recorded as
  established.

## Parabolic audit

The two immediate ways of importing the known obstruction are now closed.
`sp4-maximal-parabolics-contain-no-isw-affine-subgroup` proves that neither
the Siegel nor Klingen parabolic contains the standard
`Z^2 rtimes F_2` obstruction group.  More strongly,
`isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals` computes
that the Levi-invariant scalar `H^2` of either radical is finite.  Hence no
pointwise-trivial sequence can remain nontrivial on the relative-`(T)`
radical, so ISW Theorem A itself cannot be rerun there.  The global subgroup
shortcut is now closed as well: `sp4-contains-no-isw-affine-subgroup`
proves that every hypothetical standard `Z^2 rtimes F` copy is virtually
forced into a rational Klingen or Siegel parabolic and hence cannot exist.
The remaining published refutation possibility is the operator-valued
mechanism of ISW Theorem C with new coefficient and embeddability input.

The other proposed scalar shortcut is closed universally:
`sp4-metaplectic-class-pointwise-coboundary-limit` proves that
`B^2(Gamma,T)` is pointwise closed for every discrete group.  Hence a fixed
metaplectic class cannot supply the pointwise-trivial sequence in ISW
Theorem A merely by changing representatives.

## Theorem A surface closed uniformly (2026-08-21)

The scalar refutation route is now DEAD for every subgroup at once.
`sp4-fd-projective-multiplier-is-finite` proves that the subgroup of
`H^2(Sp_4(Z),T)` realizable by finite-dimensional projective unitary
representations is finite (Deligne via Stover arXiv:2407.07680 Thm 1.5,
plus rank one of `H_2` via Igusa/Hain arXiv:math/0203057, plus Bender's
finite presentation), and `isw-theorem-a-has-no-data-on-sp4-lattice`
concludes that no sequence satisfying the three hypotheses of ISW
Theorem A exists on `Sp_4(Z)` for ANY subgroup `Lambda` — Siegel pair,
Klingen pair, Klingen center (`klingen-center-kills-isw-condition-one`:
`H^2(Z,T) = 0`), or `Lambda = Gamma` itself.  Relative property (T) was
never the bottleneck: `Sp_4(Z)` is Kazhdan, so every sub-pair has it.
The sub-pair EXTENSION question (do NPS/theta classes of the Klingen or
Siegel pair extend to fd-realizable `Sp_4(Z)`-classes tending to the
trivial class?) is answered NO wholesale, and
`isw-corollary-b-uses-only-the-standard-area-cocycle` verifies at the
source that Corollary B's engine (the invariant area form of the
standard module) has no Siegel analogue.  The ONLY remaining published
refutation mechanism is ISW's operator-valued Theorem C: a p.m.p.
action with cocycles in `Z^2(Gamma, L^0(X,T))`, `||c_n - 1||_2 -> 0`,
non-coboundary restrictions, and — for LLP rather than LP —
`R^omega`-embeddability of every twisted crossed product
`L^infty(X) x| Gamma`.  That mouth is parked as the open claim
`sp4-isw-theorem-c-embeddable-twist-data-exists`: the cocycle half is
essentially supplied by the Deligne circle over the Bernoulli action
(Jiang's embedding), so the whole question is the Connes-embeddability
of the Maslov-twisted crossed products — which the multiplier
finiteness shows cannot be certified through finite models; note ISW
Remark 1.1 (LP would force `H^2(Gamma, L^0(X,T))` countable for every
ergodic p.m.p. action) marks the same frontier from the other side.

- **Why no exotic `SL_3(Z)` sits inside `Sp_4(Z)` (2026-08-21 audit).**
  The "alive only at `g = 2`" scoping needs that `Sp_4(Z)` contains no
  copy of `SL_3(Z)` at all, not merely none in the obvious parabolics.  A
  faithful four-dimensional representation of `SL_3(Z)` has infinite
  image, hence by Margulis superrigidity is the restriction of a rational
  representation of `SL_3`, i.e. `std (+) triv` or its dual; and
  `Lambda^2(std (+) triv) = std^* (+) std` contains no trivial summand, so
  no `SL_3(Z)`-invariant symplectic form exists on `Z^4`.  Hence
  `SL_3(Z)` does not embed in `Sp_4(Z)`, and the ISW subgroup fence does
  not reach `g = 2`.

- **Theorem C on the parabolics: toll gone, radical data dead (2026-09-17,
  swarm-0917-w4-nh-sp2g-llp).**
  `amenable-by-virtually-free-twisted-crossed-products-are-ce` proves that
  every `L^infty(X) x|_{sigma,c} P` with `P` amenable-by-virtually-free is
  Connes embeddable (averaging over the kernel, then Brown--Dykema--Jung
  Cor. 4.5).  So on `P_S` and `P_K` the ISW Theorem C moreover clause is
  automatic, and Theorem C data there would refute this node through subgroup
  permanence alone.
  `sp4-parabolic-radical-theorem-c-data-dies` proves that such data never lives
  on a subgroup `Lambda` of either radical, for any action.  The stabilizer
  field splits into three cases: free (CFW), central `mZ` (the commutator with
  the central element is a 1-cocycle on `P`, and relative (T) trivializes it),
  and finite index (Shapiro, then finitely many Levi-invariant characters of
  `H_2`).  What survives on parabolics is only the torsion-Levi residue:
  `Lambda` with finite nontrivial Levi image of order `d <= 12` and `d`-torsion
  classes killed by restriction to `Lambda cap R`.  This node stays OPEN.

- **Theorem C on the parabolics: torsion-Levi residue empty (2026-09-17,
  swarm-0917-w5-nh-sp2g-llp).**  `sp4-parabolic-theorem-c-data-dies-for-every-lambda`
  closes the residue above.  ISW Theorem C data `(P, Lambda, sigma, c_n)` does
  not exist for any finite-index `P <= P_S` or `P <= P_K`, any `Lambda <= P`
  with `(P, Lambda)` relative (T), and any action.  The new input is a
  Levi-coset counting lemma.
  - When the radical stabilizer is trivial or central, the full `P`-stabilizer
    cannot contain an element whose Levi image acts nontrivially on `V`: its
    `R`-conjugates index infinitely many a.e. disjoint fixed sets of equal
    measure.  So the isotropy lies in `Z_R . {+-I_4}`, which is central.
    Commutator 1-cocycles, relative (T) and CFW on `Lambda/W` then kill every
    class.
  - For finite orbits the restriction kernel to `Lambda_1 cap R` is finite (the
    Levi image is finite).  Compactness of `B^2` makes coboundaries open, and
    pointwise convergence finishes.

  So Theorem C through a parabolic is dead as a class, and the Connes-embeddability
  toll removed on parabolics buys nothing.  The only Theorem C mouth left is
  `sp4-isw-theorem-c-embeddable-twist-data-exists`: `Lambda` whose relative (T)
  in `Sp_4(Z)` is not relative (T) inside any containing parabolic, e.g.
  `Lambda = Gamma`.  There the toll is not free.  Separately recorded, not
  written as a node: the finite-dimensional block corona
  `C^*(Gamma)/(+)_pi M_{d_pi}` of any infinite hyperlinear Kazhdan group has the
  hyperlinear, non-amenable trace `tau_lambda` (Kazhdan HS argument plus Fell
  isolation), so it fails the LLP.  But the block extension is min-inexact by
  Wassermann's Kazhdan-projection element (as in
  `kazhdan-fd-block-representation-algebras-are-not-exact`), so this failure
  never descends to `C^*(Gamma)`.  This node stays OPEN.
