---
rg: 2
id: leavitt-kernel-annihilator-strict-self-embedding
kind: claim
title: A four-site automaton strictly embeds a proper subshift over the Leavitt unit group
distinct_from:
  level-shift-obstruction: that is about level shifts inside the Leavitt grading; this is about a shift-equivariant map of configuration space over the unit group, and its content is dynamical rather than graded
  leavitt-unit-group-nonsurjunctive: that is the open question about the whole full shift over the same group; this is an established theorem about one proper invariant subshift of it, and by subshift-self-embedding-carries-no-surjunctivity-content it is not a step toward that one
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
  - GroupApproximation/Leavitt/UnitAdditiveSpan.lean
---

Let `R = L_(F_2)(1,2)`, `G = R^x`, `S = F_2[G]`, `pi : S ->> R` the
evaluation map and `K = ker(pi)`.  Identify `S^*` with the full shift
`F_2^G` by `x(g) = x([g])`, and put

    X = K^perp = {x in F_2^G : x(k) = 0 for all k in K}.

Then `X` is a **proper** closed `G`-invariant linear subshift, and the
four-site linear rule

    (T_a x)(g) = x(g uv) + x(g u) + x(g v) + x(g w),
    u = 1 + s_0^2 t_1,   v = 1 + s_1 t_0,   w = 1 + s_0 s_1 t_1,

(all four of `uv, u, v, w` are units of `R`, hence elements of `G`) maps `X`
into `X` and restricted to `X` is **injective and not surjective**.

This is the strongest correct dynamical statement the repository's Leavitt
code supports.

## It is not a step toward Gottschalk

Surjunctivity concerns the whole full shift `A^G`, not invariant subshifts,
and the gap is not technical: the same construction runs over a finitely
generated free group, which is surjunctive.  See
`subshift-self-embedding-carries-no-surjunctivity-content`, which invalidates
the route that tries to make this claim do that work.  On the full shift this
particular `T_a` is not even injective, since `a` has four terms and hence
augmentation `0`.

The honest reading is that the interesting content sits one level down, in
whether some lift of `s_0` is left-invertible in `F_2[G]`
(`left-invertible-lift-of-s0-in-leavitt-group-algebra`) — a question about
the group algebra, on which the subshift picture is silent.

## Relation to the ring shift endomorphism

`ShiftEndomorphism.lean` proves that `r |-> s_0 r t_0 + s_1 r t_1` is an
injective non-surjective ring endomorphism.  That is a structurally similar
object and is **not** used here: a ring endomorphism is not a cellular
automaton on a full shift, and no implication between the two is available.
