---
rg: 2
id: skeleton-relative-hs-stability-for-sl2
kind: claim
title: SL2(Z[1/2]) is HS-stable relative to its two exact parabolic skeletons
distinct_from:
  approximate-doubling-invariant-joint-measure-is-atomic: that is the target common-odd-model statement; this is the residual gluing problem after Levit--Vigdorovich exactifies both parabolic BS(1,4) skeletons, and it is strictly smaller than raw stability because the remaining freedom lives in compact centralizer torsors of exact finite-order data.
  iwahori-outlier-repair: that is the far-sector endpoint in square-root form; this isolates the one new stability ingredient the skeleton synthesis needs, with the alignment steps and the odd-collapse endgame already supplied by finite arguments and established nodes.
  odd-congruence-vertex-sector-admits-no-exact-leak: that consumes a common odd model to kill the leak by co-density; this produces the common odd model from the skeletons.
---

Let `pi` be an asymptotic finite-dimensional representation of
`SL_2(Z[1/2])`.  By Levit--Vigdorovich (arXiv:2206.02268, Cor D(3);
`BS(1,4)` is HS-stable), each parabolic skeleton
`(pi(u), pi(h))` and `(pi(l), pi(h))` is HS-close to an EXACT
`BS(1,4)` pair whose base unitary has finite ODD order.  CLAIM: the
two exact skeletons can be corrected further, with dimension-free
loss, so that ALL of the following hold exactly on a common model:
a single `h`-component shared by both skeletons; an intertwiner
implementing the Weyl swap; and the Weyl element expressed as its
defining word in the two parabolics.  Equivalently: `SL_2(Z[1/2])` is
HS-stable RELATIVE to exact skeleton data.

Why this is strictly smaller than raw HS-stability: after the two
skeletons are exact, the remaining freedom is (i) the relative
position of two exact finite-odd-order structures — spectra align by
Hoffman--Wielandt, a finite problem — and (ii) gluing corrections
ranging over the CENTRALIZER TORSORS of the exact skeletons, which
are compact groups; the obstruction theory is an alignment/cohomology
problem over compact torsors rather than a stability problem over all
of `U(d)`.

Consequence chain if established:
`skeletons exact (LV) + this claim` gives the common finite ODD model
of `approximate-doubling-invariant-joint-measure-is-atomic`; on an
odd model conjugation by `diag(2, 1/2)` is INNER, co-density applies,
and the leak collapses by the mechanism of
`odd-congruence-vertex-sector-admits-no-exact-leak` — the far sector
closes, `iwahori-outlier-repair` resolves, and the goal follows
through the Iwahori route.  The two-adic content that obstructs
everything elsewhere is absent here by construction: the
Levit--Vigdorovich skeletons are odd, and multiplication by four is
an automorphism on odd spectra, so the conductor-box escape mechanism
never activates.

## Attempts

- **The torsor reduction is the designed attack.**  Fix the exact
  `u`-skeleton `(V_0, W_0)`.  The second skeleton's `h`-part `W_0'`
  satisfies `||W_0' - W_0|| = o(1)`; correcting `W_0'` to `W_0`
  within exact `BS(1,4)`-pairs is a RELATIVE stability question for
  `BS(1,4)` over its `<h>`-subgroup — plausibly accessible by the
  same dense-periodic-measure technique, conditioning the Marcus
  argument on the `h`-component.  Then the Weyl word
  `s = e_12(1) e_21(-1) e_12(1)` is DETERMINED by the exact data, and
  the final consistency (that the determined `s` approximately
  implements the swap it must) is a closed condition on the compact
  torsor of gluings — a fixed-point/averaging problem on a compact
  group, where dimension-free tools (Gowers--Hatami on the finite odd
  model's image, the (tau) squeeze) are available.
- **Proof-plan and its precise load-bearing step (2026-08-21, same
  day).**  The natural plan: (1) extend Levit--Vigdorovich from
  `BS(1,4)` to the full solenoid group `Q = Z[1/2] rtimes_4 Z`
  (their own mechanism should carry: characters of `Q` are
  `x4`-invariant measures on the compact solenoid, where hyperbolic
  specification makes periodic measures dense — Sigmund, as the far-
  sector node already records); (2) align the exact structures; (3)
  finite Steinberg rank-one bookkeeping: with both towers exact and
  the Weyl word determined, the presentation of `SL_2(Z[1/2])` closes
  and the tuple is an exact representation.  Steps (1) and (3) are
  standard-shaped.  The load-bearing step is (2), and the naive
  argument FAILS precisely here: Folner averaging aligns two close
  exact representations only with loss (generator closeness) x
  (Folner diameter), and `Q` has exponential growth, so
  small-boundary Folner sets have huge diameter.  What (2) actually
  needs is LOCAL HS-RIGIDITY of the exact representation spaces of
  `BS(1,4)`/`Q`: two exact finite-dimensional representations that
  are HS-close on generators are conjugate by a small unitary.  This
  is a strengthening of stability (stability = approximate implies
  near SOME exact; local rigidity = the exact variety has no
  HS-nearby disconnected sheets), plausibly attackable by the same
  periodic-measure technology since close representations have close
  weights on periodic characters.  If local rigidity fails, the
  gluing may genuinely branch, and the route dies here — a clean,
  falsifiable crux.
- **Second correction: step (3) is not bookkeeping (2026-08-21,
  same day).**  Rank-one Steinberg presentations have NO commutator
  formula between opposite root groups; the `w(u)`-conjugation
  relations for a generating set of units are INDEPENDENT axioms.
  For `Z[1/2]` the units are generated by `2` (and `-1`), so the
  aligned tuple must satisfy TWO swap constraints — the `w(1)`-swap
  and the `w(2)`-swap — and the second is not implied by the first
  plus the towers.  The gluing crux is therefore the SIMULTANEOUS
  small-conjugacy of the two exact odd towers under both Weyl words
  at once; their ratio `w(2) w(1)^{-1} = h` is exactly the Iwahori
  square-root object, so this route lands on the classical hard core
  in new coordinates: two exact odd solenoid towers, two swap
  alignments over compact centralizer torsors, all two-adic escape
  disabled.  The coordinates are sharper than any prior form of the
  far sector (local HS-rigidity of the solenoid variety plus a
  two-swap simultaneous alignment, both clean compact-space
  questions), but the difficulty is conserved, as it must be.
- **Leg (1) closed; the tower exactifies top-down (2026-08-21).**
  `bs14-exact-representation-variety-is-hs-locally-rigid` is
  established, and with it the solenoid tower needs NO new stability
  theorem: exactify the DEEPEST level required by the relator family
  via Levit--Vigdorovich, then define the whole tower downward by
  fourth powers of that single exact pair — an exact solenoid
  representation sharing one `h`, with errors amplified by `4^depth`
  but depth is fixed per relator, which is all an asymptotic
  representation owes.  So per-relator solenoid exactification holds
  with fixed-depth constants, full uniform `Q`-stability is not
  needed, and BOTH parabolic towers exactify with shared internal
  `h`-components.  The claim's entire remaining content is the
  TWO-SWAP SIMULTANEOUS ALIGNMENT: correct the relative position of
  the two exact odd towers so that the `w(1)`- and `w(2)`-Weyl words
  act exactly at once — the Iwahori square-root core in exact-odd
  coordinates, now provably the LAST piece of this route.
- **Where the obvious attack could die.**  If the torsor fixed-point
  problem has an obstruction class that grows with the odd order,
  the loss would not be dimension-free; the analogue at the level of
  finite models is a cohomology comparison for
  `SL_2(Z/m)`-extensions, uniform in odd `m` — Selberg/(tau) should
  control it, but this is exactly the step that must be written.
