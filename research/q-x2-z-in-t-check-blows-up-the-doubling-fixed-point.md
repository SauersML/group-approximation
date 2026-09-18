---
rg: 2
id: q-x2-z-in-t-check-blows-up-the-doubling-fixed-point
kind: claim
title: In every copy of Q x|_2 Z in T-check the doubling semiconjugacy blows up its fixed point to an interval, so the copy of Q never acts minimally
distinct_from:
  q-x2-z-in-t-check-has-a-doubling-semiconjugacy: that constructs the semiconjugacy h and proves it nowhere affine; this uses it to exclude every copy whose fibre h^-1(0) is a single point, including every minimal one.
  t-check-contains-q-rtimes-2-z: that is the open existence question; this reduces it to the blown-up case.
  pp-circle-divisible-subgroups-act-freely: that shows divisible subgroups of piecewise-projective circle groups act freely; this is about minimality of the free action of Q x|_2 Z on the line, in a group containing a dilation.
---

**ESTABLISHED** through `q-x2-z-in-t-check-blows-up-the-doubling-fixed-point-proof`.
Not independently reviewed. No priority is claimed. The proof uses standard facts of
one-dimensional dynamics, cited in the proof.

## Statement

Let `D ≅ (Q,+)` and `t` in `T-check = <T-bar, x -> 2x>` satisfy `t q t^-1 = q^2`
(`q in D`). Let `h` be the doubling semiconjugacy of
`q-x2-z-in-t-check-has-a-doubling-semiconjugacy`, normalized there. Then:

1. `P := h^-1(0)` is a nondegenerate closed interval, and `t(P) = P`.
2. For every `s in Q`, the fibre `h^-1(s) = q_s(P)` is a nondegenerate interval,
   where `q_s in D` has translation number `s`. `D x| <t>` permutes these fibres by its
   affine action on `Q`.
3. `D` does not act minimally on `R`, and `h` is not injective.

## What is left

Any copy of `Q x|_2 Z` in `T-check` is a "blown-up" one.
- The circle map `u` induced by `t` carries a family of nondegenerate intervals
  `F_s`, one for each rational `s`.
- `u` maps `F_s` homeomorphically onto `F_(2s)`, and permutes periodically those
  of odd denominator.
- `D` translates the family.
- The rest of the circle is a closed set `K'` on which `u` is semiconjugate to
  `θ ↦ 2θ`.

This case is open (`t-check-contains-q-rtimes-2-z`).
