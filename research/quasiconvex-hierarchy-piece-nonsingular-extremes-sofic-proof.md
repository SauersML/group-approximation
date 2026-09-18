---
rg: 2
id: quasiconvex-hierarchy-piece-nonsingular-extremes-sofic-proof
kind: route
title: Linton's quasi-convex Magnus subgroups plus Haglund--Wise separability supply the separable-piece hypothesis of the shift dictionary
target: quasiconvex-hierarchy-piece-nonsingular-extremes-sofic
requires:
  - nonsingular-magnus-extremes-separable-piece-sofic
  - linton-z-stable-one-relator-hierarchy-theorem
---

Date: 2026-09-17. Written proof, not a Lean certificate.

## Sources (read at source on 2026-09-17)

- **[Lin]** M. Linton, *One-relator hierarchies*, arXiv:2202.11324v3; Duke
  Math. J. 174 (2025). Theorem 7.1 and its proof (p. 31), Theorem 7.2 (p. 31),
  Definition 5.8 (p. 22), and the definition of one-relator complexes and
  Magnus subgraphs (section 2.2, p. 7). The Theorem 7.1 statement is already
  imported in [[linton-z-stable-one-relator-hierarchy-theorem]]. The proof
  text reads: "assuming `pi_1(X)` is hyperbolic and the hierarchy is
  quasi-convex, `pi_1(X)` is virtually special by [Wis21, Theorem 13.3] and
  the image of `pi_1(A)` in `pi_1(X)` is quasi-convex for any connected
  subcomplex `A in X_i` by Theorem 5.9 and induction." Theorem 7.2: "Let X be
  a one-relator complex with negative immersions. Then `pi_1(X)` is
  hyperbolic, virtually special and all of its one-relator hierarchies ... are
  quasi-convex hierarchies."
- **[Wis]** D. T. Wise, *The structure of groups with a quasiconvex hierarchy*,
  Ann. of Math. Stud. 209 (2021), Theorem 13.3. A hyperbolic group with a
  quasi-convex hierarchy is virtually compact special. This is quoted through
  [Lin], not re-read here.
- **[HW]** F. Haglund and D. T. Wise, *Special cube complexes*, GAFA 17
  (2008), Theorem 1.3. If `X` is a compact special cube complex and
  `pi_1(X)` is word-hyperbolic, then every quasi-convex subgroup of `pi_1(X)`
  is separable. This is quoted from memory of the published statement, not
  re-read here.
- **[LW]** L. Louder and H. Wilton, *Negative immersions for one-relator
  groups*, Duke Math. J. 171 (2022). A one-relator complex has negative
  immersions iff the primitivity rank of its relator exceeds `2`. This is
  used only in the special case.

## Proof

Let `X` be the standard presentation complex of
`B_0 = <a_0,...,a_n | W_0>`: one vertex, loops `a_0,...,a_n`, and one 2-cell
attached along the cyclically reduced word `W_0`. The attaching map is an
immersion, so `X` is a one-relator complex in the sense of [Lin, section 2.2].

**Step 1 (quasi-convex Magnus subgroups).** By (QC) and [Lin, Theorem 7.1],
condition (3) holds, so condition (1) holds: `B_0` is hyperbolic and the
hierarchy is quasi-convex. The Moreover clause, applied with `i = 0`, says that
for every connected subcomplex `A <= X_0 = X` the image of `pi_1(A)` in `B_0`
is quasi-convex. Let `A_-` be the one-vertex subcomplex made of the loops
`a_0,...,a_(n-1)`, and `A_+` the one made of `a_1,...,a_n`. They are connected,
and by the Freiheitssatz their `pi_1` maps injectively onto `F_-` and `F_+`.
So `F_-` and `F_+` are quasi-convex in `B_0`.

**Step 2 (residual finiteness).** By [Wis, Theorem 13.3], as used in the proof
of [Lin, Theorem 7.1], `B_0` has a finite-index subgroup `B'` that is
`pi_1` of a compact special cube complex. `B'` embeds in a right-angled Artin
group, which is linear over `Z`. So `B'` and hence `B_0` are residually finite.
We may take `B'` normal by passing to its normal core, which is again the
fundamental group of a finite cover and hence of a compact special cube
complex.

**Step 3 (separability).** Let `F in {F_-, F_+}` and `F' = F cap B'`.
- `F'` has finite index in `F`, so it is quasi-convex in `B_0`, hence in the
  finite-index subgroup `B'`, which is quasi-isometric to `B_0` through the
  inclusion.
- `B'` is hyperbolic. By [HW, Theorem 1.3], `F'` is closed in the profinite
  topology of `B'`.
- `B'` has finite index in `B_0`, so the profinite topology of `B_0` induces that
  of `B'`, and `B'` is open and closed in `B_0`. So `F'` is closed in `B_0`.
- `F` is a finite union of cosets `f_i F'` with `f_i in F`, each closed. So
  `F` is closed in `B_0`.

**Step 4 (conclusion).** Steps 2 and 3 are hypothesis (S) of
[[nonsingular-magnus-extremes-separable-piece-sofic]], and (N) is assumed.
That theorem gives that `G` is sofic. ∎

**Special case.** If `X` has negative immersions, then by [Lin, Theorem 7.2]
every one-relator hierarchy of `X` is quasi-convex and `B_0` is hyperbolic. So
condition (1) of Theorem 7.1 holds for any one-relator hierarchy (one exists by
[Lin, Theorem 4.13]), and Steps 1 to 4 apply unchanged. ∎

## The locally finite alphabet needs (S): a necessity remark

In the construction of [[nonsingular-magnus-extremes-separable-piece-sofic-proof]]
the fold needs `rho(b) not in D` for the inner syllables `b in B_0 \ F_-`, where
`D = intersect_N rho(F_-) K_N`. If `rho(b) not in D`, then
`rho(b) not in rho(F_-) K_N` for some `N`, that is,
`pi_N(rho(b)) not in pi_N(rho(F_-))`. The map `pi_N o rho` restricted to `B_0`
has finitely generated image in the locally finite group `P_inf^(2N+1)`, so the
image is finite. This gives a finite quotient of `B_0` in which `b` avoids the
image of `F_-`. The same holds for `F_+` and for `b != 1`.

So for every choice of growth scheme, hypothesis (S') for the syllables that
occur is necessary for this dictionary to separate them. The theorem cannot be
iterated down the hierarchy with "sofic" in place of (S). A piece produced by
the theorem itself, such as `BS(2,3)` in a larger one-relator group, is sofic
but typically not residually finite, and then no locally finite alphabet folds
over it.
