---
rg: 2
id: kazhdan-hyperbolic-continuum-non-fng-maximal-kernels
kind: claim
title: A torsion-free hyperbolic Kazhdan group has continuum many maximal normal subgroups that are not finitely normally generated
distinct_from:
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that asks whether one SPECIAL elementary-matrix envelope has at least one finitely normally generated maximal kernel; this gives a different finitely presented Kazhdan group with continuum many maximal kernels that are not finitely normally generated, refuting only the proposed general normal-Noetherian shortcut and not the special envelope claim.
  fp-quotient-iff-kernel-finitely-normally-generated: that is the general finite-presentation equivalence for one quotient of one finitely presented group; this combines that equivalence with continuum many recent simple characteristic quotients to prove a new existence theorem about a fixed hyperbolic Kazhdan group.
  boone-higman-conjecture: that asks for a finitely presented simple envelope preserving every finitely generated solvable-word-problem input; this is an obstruction showing that even torsion-free hyperbolic property-(T) ambient groups can have continuum many maximal quotients which are not finitely presented, with no prescribed core or universal embedding statement.
artifacts:
  - research/artifacts/kazhdan-maximal-kernel-nonnoetherianity-2026-08-30.md
---

There is a finitely presented, torsion-free, non-elementary word-hyperbolic
group `H` with property `(T)` and a family `{M_i : i in I}` of cardinality
continuum such that

1. every `M_i` is characteristic in `H`, hence normal;
2. every quotient `H/M_i` is infinite, simple, torsion-free and has property
   `(T)`;
3. the quotients `H/M_i` are pairwise non-isomorphic; and
4. no `M_i` is finitely normally generated in `H`.

In particular, property `(T)` does not imply `Max-n`, even after adding finite
presentability, torsion-freeness and word-hyperbolicity.

The point relevant to Boone--Higman is deliberately narrower.  This kills the
idea that the missing kernel in
`ck-envelope-has-a-finitely-normally-generated-maximal-kernel` follows from a
general Kazhdan normal-lattice Noetherianity theorem.  It does **not** rule out
finite normal generation for one specially chosen maximal kernel of that
particular elementary-matrix envelope.
