---
rg: 2
id: pl-ea-calibrators-are-nonamenable-interval-groups
kind: claim
title: A piecewise linear interval or circle group acting amenably but not extensively amenably on its breakpoints exists exactly when PL_+([0,1]) has a nonamenable subgroup, and circle worlds such as Thompson's T already fail amenability of the action
distinct_from:
  thompson-f-amenable-iff-dyadic-action-extensively-amenable: that is the breakpoint-cocycle equivalence for F on the dyadics; this extends it to every countable PL group of the interval or circle, with arbitrary real breakpoints and slopes, and adds the calibration dichotomy that locates where an F-specific input must enter.
  thompson-t-orbits-carry-no-invariant-means: that is the uniform non-invariance of finite point sets under T; this uses it only for item 5 and adds the general rotation-number structure of all PL circle groups with an amenable orbit action.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that proves amenability of end-rigid Schreier graphs of F by x_0-rays; this proves amenability of every orbit action of every subgroup of PL_+([0,1]) through the abelian germ group at the infimum of the orbit.
  amenable-infinite-simple-circle-groups-fix-a-point: that forces a global fixed point for amenable simple circle groups; this assumes only an amenable orbit action (not an amenable group) and gets a point-fixing kernel of the rotation-number homomorphism.
  f-functor-cocycles-need-an-exotic-recurrent-action: that kills functor cocycles on actions where F acts unfaithfully or recurrently; this calibrates the faithful breakpoint action itself against neighbouring PL worlds.
  f-dyadic-inverted-orbit-is-subballistic-on-rare-events: that is the open confinement statement for F; this shows no PL world can currently serve as a counter-calibration for it, and that T's failure of confinement is a Kesten-level failure of amenability of the orbit action.
---

**ESTABLISHED** through `pl-ea-calibrators-are-nonamenable-interval-groups-proof`.

**Setting.** `PL_+(I)` is the group of orientation-preserving homeomorphisms of `I = [0,1]` that are piecewise
affine with finitely many breakpoints; breakpoints are any reals and slopes any positive reals. `PL_+(S^1)` is
the group of orientation-preserving homeomorphisms of `S^1 = R/Z` whose lifts to `R` are piecewise affine with
finitely many breakpoints per period. For `g` in either group, `bp(g)` is the set of points where the two
one-sided slopes of `g` differ (endpoints of `I` excluded). For a group `G` of such maps put
`B(G) = ⋃_{g ∈ G} bp(g)`. Extensive amenability (EA) is Definition 1.1 of Juschenko–Matte Bon–Monod–de la Salle,
imported in `affine-lamplighter-amenable-iff-extensively-amenable`.

1. **Breakpoint equivalence.** Let `G ≤ PL_+(I)` or `G ≤ PL_+(S^1)`. Then `B(G)` is `G`-invariant, and if
   `B(G) ≠ ∅`, `G` is amenable if and only if `G ↷ B(G)` is extensively amenable.
2. **Every interval orbit action is amenable.** If `G ≤ PL_+(I)` and `Y ⊆ I` is nonempty and `G`-invariant,
   then `G ↷ Y` is amenable. In particular `G ↷ B(G)` is amenable whenever `B(G) ≠ ∅`.
3. **Circle orbit actions are amenable only through a fixed point.** If `G ≤ PL_+(S^1)` and `G ↷ Y` is amenable
   for some nonempty `G`-invariant `Y ⊆ S^1`, then `G` preserves a Borel probability measure `μ` on `S^1`, the
   rotation number `rot : G → R/Z` is a homomorphism, and its kernel `K` fixes `supp μ` pointwise. So `K` is
   conjugate by a rotation into `PL_+(I)`, `G/K` is abelian, `G` is amenable iff `K` is, and `G` has no
   non-abelian free subgroup.
4. **Calibration dichotomy.** The following are equivalent.
   - (a) Some group `G ≤ PL_+(I)` or `G ≤ PL_+(S^1)` with `B(G) ≠ ∅` acts amenably, but not extensively
     amenably, on `B(G)`.
   - (b) `PL_+(I)` has a nonamenable subgroup.
5. **Thompson's T.** Let `G ≤ T` contain the rotations `r_{1/4}`, `r_{1/2}` and the element `x_0`. For every
   nonempty `G`-invariant `Y ⊆ S^1`, `G ↷ Y` is neither amenable nor extensively amenable. In particular
   `T ↷ D/Z` (the dyadic points of the circle) is not EA, `F = Stab_T(0)` is not co-amenable in `T`, and for
   `G_3 = ⟨r_{1/4}, r_{1/2}, x_0⟩`, `Y = G_3·0` and any symmetric finitely supported `μ` with generating support,
   there is `ε > 0` with `P(|O_n| < εn) ≤ e^{−εn}` for all large `n` (inverted orbit `O_n` as in
   `f-dyadic-ea-iff-inverted-orbit-confinement`).

**What this calibrates and kills.**
- *Circle worlds die before the EA step.* The invariant is the rotation-number homomorphism with point-fixing
  kernel (item 3). Every PL circle world without it (Thompson's `T`, any PL circle group with a non-abelian free
  subgroup, any containing a dense rotation group and a map that does not preserve Lebesgue measure) fails at
  *amenability of the orbit action*. EA implies amenability of the action (JMBMdlS Lemma 2.1), so such worlds
  separate `F ↷ D` only from arguments that never use amenability of the Schreier graph. Using `T` to calibrate
  inverted-orbit confinement is void: for `T` the exponential confinement bound is a consequence of
  nonamenability of the orbit action, not a large-deviation effect of lamps.
- *Interval worlds cannot calibrate without a counterexample.* By items 1 and 2, every countable `G ≤ PL_+(I)`
  shares with `F ↷ D` amenability of the breakpoint action, the end-germ Følner rays at the infimum of each orbit,
  and the breakpoint cocycle with trivial kernel. A method that proves EA of `F ↷ D` from properties shared by all
  such breakpoint actions proves that every subgroup of `PL_+(I)` is amenable (Stein groups, `F_τ`, groups with
  irrational slopes). By item 4, a PL world that separates amenability from EA on breakpoints exists iff a
  nonamenable subgroup of `PL_+(I)` does. No such subgroup is recorded in the graph.
- *Where the F-specific input must enter.* A proof of `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`
  that is not a proof for all of `PL_+(I)` must use an input that fails for some subgroup of `PL_+(I)`: dyadic
  arithmetic of breakpoints and slopes, finite presentability, or a statement about specific generators. Currently
  no PL world can test such an input.

Not covered: Ore window profiles, density families and C*-simplicity of `T` are not calibrated here.
