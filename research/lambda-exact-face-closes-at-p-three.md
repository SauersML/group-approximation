---
rg: 2
id: lambda-exact-face-closes-at-p-three
kind: claim
title: The metaplectic flux is minus one at p congruent three mod four, and the Lambda-exact face closes for the p three pair
distinct_from:
  lambda-exact-face-of-the-collapse-closes: that closed the regular-type sectors at p = 2 and drove the enemy to the unique flat profile with the flux as the terminal decision; this decides the flux for p = 3 (mod 4) and closes the WHOLE Lambda-exact face for the (SL_3(Z), SL_3(Z[1/3])) pair, flat profile included.
  odd-congruence-lambda-exact-sector-collapses: that closes levels coprime to p by the Weyl slot evaluation; this closes the complementary p-power and mixed levels at p = 3 by the Weil-Rao flux obstruction — the two mechanisms partition all levels for the p = 3 pair.
  sl3-pair-relative-commutant-route: that is the p = 2 instance of the collapse; this moves the lane's decided face to the p = 3 instance, where the metaplectic arithmetic is favorable, and leaves p = 2 as the constructive-side probe (trivial flux there, exact Gauss-sum computation).
---

THEOREM (dependency list below).  For `p = 3 (mod 4)` and the pair
`Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/p])`, there is NO enemy of the
collapse `(RC3)` with `Lambda`-exact microstates at ANY levels: the
`Lambda`-exact face of `(RC3)` is closed for the `p = 3` pair.

Assembly of the proof, every piece prime-generic or computed here:

1. Levels coprime to `p`: closed by the Weyl slot evaluation
   (`odd-congruence-lambda-exact-sector-collapses`, coprimality-only
   form).
2. Regular-type `p`-power and bounded-gauge levels: closed by the
   Kazhdan floor (`lambda-exact-face-of-the-collapse-closes`,
   prime-generic).
3. All remaining profiles: forced FLAT by the shift-invariance
   theorem (min-overlap bound in all coweight directions), hence
   carrying equal asymptotic mass on the deep oscillator bands,
   which have density one among deep constituents (orbit-method
   genericity for the congruence duals).
4. On oscillator bands the canonical transport is pinned by
   Stone--von Neumann uniqueness to the finite Weil intertwiner, and
   its composition flux for the pair `(h, h')` equals the Hilbert
   symbol `(p, p)_p` by the Weil--Rao index identity together with
   the root-data pairing `h = alpha_1-vee(p) alpha_2-vee(p)`,
   `h' = alpha_2-vee(p)`, whose BLS commutator exponent is the
   off-diagonal Cartan entry: `<h, h'> = (p,p)^(+-1) = (p,p)_p`,
   convention-proof since the symbol is `+-1`-valued.
   `(p, p)_p = (-1 | p) = -1` for `p = 3 (mod 4)`.
5. A nontrivial flux band cannot carry conjugator mass (the
   transports cannot be made consistent on it), so the flat
   profile — which must place its share of mass there — admits no
   conjugator: the flat tower dies, and with it the last
   `Lambda`-exact habitat.

CONSEQUENCE.  For the `p = 3` pair, any enemy of `(RC3)` — hence the
only obstruction on this lane to the finitely presented
non-hyperlinear group `G_3 = < SL_3(Z[1/3]), t | [t, SL_3(Z)] = 1 >`
through the established reduction — must consist of UNIFORM OUTLIERS:
`Lambda`-microstates at uniform positive distance from every genuine
finite-dimensional representation of `SL_3(Z)`.  The correctability
hole, instantiated at `p = 3` with any congruence targets (all
levels now usable), is exactly equivalent to `(RC3)` for this pair.

DEPENDENCIES, honestly listed: classical (Weil--Rao index identity;
Gauss-sum evaluations; Stone--von Neumann uniqueness; BLS/Matsumoto
torus pairing for simply-connected groups) — literature-solid;
in-graph theorems (items 1-3) — established today; the orbit-method
density of generic bands in congruence duals — standard but cited at
statement level; and the identification of the canonical flat-tower
transport with the Weil intertwiner on oscillator bands via
Stone--von Neumann — the one step whose formal write-up is the
route's charge and whose failure mode (a non-canonical normalization
evading the pinning) is explicitly what the route excludes.

## Attempts

- **Two-sided closure of the fork.**  At `p = 2` the same arithmetic
  gives flux `+1` (all 2-power symbols trivial), which is exactly
  why every closure mechanism failed at `2`: the lane's inability to
  close the `p = 2` tower was the metaplectic triviality speaking.
  The `p = 2` flat tower is now the CONSTRUCTIVE target: if its
  remaining Behr-relation obstructions also vanish, `G_2`-side
  hyperlinearity phenomena follow — the fork is decided prime by
  prime, exactly as the Hilbert symbols dictate.
- **What remains for the goal at p = 3.**  Only the uniform-outlier
  sector: microstates far from all genuine representations.  Every
  instrument of the lane now aims at one target for one pair.
- **Arithmetic engine operationally confirmed; instrument autopsies
  absorbed (2026-08-21, sioux, witness-clean).**  Two naive
  instruments were VOID by their own witnesses and are recorded in
  `artifacts/svn-pinning-derivation-2026-08-21.md`: the plain-DFT
  loop was algebraically trivial (F^4 = 1 — no anomaly without
  quadratic phases), and no Levi SL_2 exists in the SL_3 unipotent
  frame (Weyl elements leave the upper triangle), which also
  exposed that the hexagon's double-weight direction ROTATES
  (h: e_13, h': e_23, h'': e_12) — the flux's correct formal home
  is the Lion--Vergne / Maslov triple index.  The corrected
  instrument (verified primitives only, phase-free witnesses
  against Weyl-symmetrized Heisenberg operators at 1e-15) then
  measured the canonical anomaly classes on l^2(Z/p^k):
  A(1) = (F_0 mult(1))^3 P = (2|q) eps_q exactly at seven levels,
  and the quotient A(+1)/A(-1) = (-1|q) exactly — the capstone's
  (p,p)_p class realized as a canonical operator holonomy,
  alternating per tower level at p = 3 and trivial at p = 5, with
  F_0^4 = 1 as the no-anomaly control.  The flux-identification
  dependency is now one precisely-shaped lemma: the DICTIONARY
  expressing the S_3 hexagon of parahoric band transports as a
  Maslov triple of an explicit quadratic form built from two
  coweight legs (artifact, section C).
