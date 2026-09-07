---
rg: 2
id: nonsingular-equations-preserve-matrix-certificates
kind: claim
title: Nonsingular unitary equations preserve coefficient matrix certificates exactly
distinct_from:
  mf-radical-words-have-linear-certificates: that characterizes which old words admit operator-norm certificates; this proves that adjoining a nonsingular equation leaves their entire set of constants unchanged, even at a fixed matrix size.
  hyperlinear-radical-has-linear-word-certificate: that characterizes HS radical membership; this proves exact invariance of the coefficient energy inequalities under nonsingular one-variable adjunction.
  window-controlled-finite-dimensional-root-theorem: that seeks suitable approximations for arbitrary coefficient groups; this solves the root equation exactly after a unitary coefficient tuple is already given, without asserting such approximations exist for every group.
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
---

For every `d>=1`, every unitary word map with one variable of nonzero
exponent sum `m` has degree `m^d` and is onto `U(d)`. This is the classical
Gerstenhaber--Rothaus assertion, with a complete one-variable degree proof
in the artifact. Thus for a word `w(S,t)` nonsingular in `t`, projection
of `w(U,T)=I` onto all coefficient tuples `U in U(d)^S` is surjective.

For every finite old relator list `R`, old word `a`, and `C>=0`, the
universal operator-norm inequality `d_a(U)<=C max_R d_r(U)` holds if and
only if `d_a(U)<=C max(max_R d_r(U),d_w(U,T))` holds. Likewise,
`e_a(U)<=C sum_R e_r(U)` holds if and only if
`e_a(U)<=C(sum_R e_r(U)+e_w(U,T))` holds, where `e` is squared normalized
HS displacement. Each equivalence holds in any one fixed dimension as
well as uniformly over all dimensions, including an empty old relator list.
Consequently the optimal constants are exactly conserved.

If an old word dies by a normal-closure identity using `A` occurrences of
old relators and any number of the new nonsingular relator, it has the
old-relator norm bound (12) and weighted energy bound (13) of the artifact.
This is a necessary condition on a counterexample identity; none is supplied.
