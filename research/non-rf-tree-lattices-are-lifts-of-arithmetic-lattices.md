---
rg: 2
id: non-rf-tree-lattices-are-lifts-of-arithmetic-lattices
kind: claim
title: The small non-residually-finite lattices in products of trees with a PGL_2(F_q)-type local action on one factor are free-kernel lifts of arithmetic lattices
distinct_from:
  radu-horizontal-quotient-is-arithmetic-lattice: that proves the lift structure for Radu's BMW lattice; this asks whether it holds for the Janzen-Wise lattice and Radu's (4,4)-group, whose local actions have the same shape
  burger-mozes-infinitely-transitive-tree-groups: that imports Burger-Mozes structure theory, where discrete normal subgroups of locally quasiprimitive closures are trivial; this concerns lattices whose other closure is not locally quasiprimitive, where a projection can have a large free kernel
---

**OPEN.** Let `Γ` be the Janzen–Wise lattice
`<a,b,x,y | axay, ax^(-1)by^(-1), ay^(-1)b^(-1)x^(-1), bxb^(-1)y^(-1)>`
(Titz Mite–Witzel arXiv:2509.05054v2, Proposition 3.8, p. 11–12, not residually finite with
`[x^3, y^4]` in the finite residual). The conjecture is that its horizontal tree action factors
through a representation into `PGL_2` over a number field, with `3`-adic Bruhat–Tits tree
`T_4`. Then `Γ` is an extension of a free group by an arithmetic group, as proved for Radu's
BMW lattice in `radu-horizontal-quotient-is-arithmetic-lattice`. The same question applies to
Radu's torsion-free `(4,4)`-group `Γ_(4,4)` (arXiv:1712.01091, Prop. 5.1).

If true, the known small non-residually-finite irreducible lattices would share one
mechanism. On one factor the local action is `PGL_2(F_q)`-like and the closure is a p-adic Lie
group. On the other factor the local action is imprimitive, and the lattice is the lift of an
arithmetic lattice along the Cayley graph of its vertex group.

## Attempts

* **Local actions (computed by hand from the four relators).** Each relator
  `h_1 v_1 h_2 v_2 = 1` gives four corner identities `h v = v' h'`.
  * *Vertical tree.* The horizontal letters act on the vertical labels as
    `a ↦ (x y^(-1))(y x^(-1))` and `b ↦ (x y x^(-1) y^(-1))`, generating `D_4`. That is
    transitive, imprimitive, and not quasiprimitive, since `b^2` is normal and intransitive.
  * *Horizontal tree.* The vertical letters act on the horizontal labels as
    `x ↦ (a a^(-1) b)` and `y ↦ (a a^(-1) b^(-1))`, generating `Alt(4) ≅ PSL_2(F_3)` on the
    four points. This is the local action of `PSL_2(Q_3)` on `T_4`.
  * *Comparison.* This is the shape of Radu's BMW lattice (`C_2` against
    `S_3 = PGL_2(F_2)`) and of `Γ_(4,4)` (`D_8` against `Alt(4)`).
* **Unconstrained numeric search (2026-09-13).** Gauss–Newton over `PSL_2(C)^4` from 400 random
  starts, requiring all four relators to be `±I`, found only a degenerate component: every
  generator of trace 0 and `tr(ab) = ±2`.
* **Constrained numeric search (2026-09-13): a candidate representation.** Imposing that
  `x` and `y` have order 3 in `PSL_2`, 600 random starts converge to a single solution up to
  conjugacy.
  * *Invariants.* `tr^2 a = 8/3`, `tr^2 b = 2/3`, `tr ab = 2/3`, `tr xy = 3/2`,
    `tr^2(ax) = 3/2`, `tr^2(bx) = 1/6`.
  * *Rationality.* Over 3000 random words of length at most 8, `tr^2` is within `6·10^(−14)` of a
    rational number whose denominator involves only the primes 2 and 3. So numerically the
    adjoint trace field is `Q`, and the representation is integral away from `{2, 3}`.
  * *Tree at 3.* `a` and `b` have `v_3(tr^2) = −1`, so they are hyperbolic of translation
    length 1 on the tree of `PGL_2(Q_3)`, moving the base vertex to a neighbour, as horizontal
    letters must. `x` and `y` are elliptic of order 3, matching the 3-cycles of the local action.
  * *Where it stands.* This is the Radu pattern, with `(Q, S = {2,3})` in place of
    `(Q(√17), S = {primes above 2})`. It is numerics only. What remains:
    * exact matrices, whose entries appear to lie in `Q(√2, √3, i)`;
    * exact relators;
    * the 3-adic tree identification;
    * the quaternion algebra over `Q` and its ramification;
    * the second tree, at 2.
  * *Seed.* The scripts are `jw_rep_search_constrained.py` and `jw_invariants.py` in lane
    `ex-tree-lattice-mixing`; seed 11.
