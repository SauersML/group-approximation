---
rg: 2
id: nonhyperlinear-from-linear-energy-domination
kind: route
title: One energy comparison closes the two-S3 collapse and the goal with it
target: non-hyperlinear-group
requires:
  - atlas-linear-energy-controlled-by-full-packet-defect
  - atlas-boundary-tangent-covariance-coercivity
  - atlas-19243-centrality-is-bar-s-consequence
  - raw-swap-forces-two-s3-covariance-energy
  - leavitt-regular-atlas-separating-refinement
  - compiled-raw-source-word-nontrivial
---

Suppose `Q = L_(F_2)(1,2)^x` is hyperlinear.  Apply
`leavitt-regular-atlas-separating-refinement` to the compiled raw source
word, nontrivial by `compiled-raw-source-word-nontrivial`: it gives canonical
regular-`A_8` models `U_n in U(20160 k_n)` with

```text
eps_n = max_(s in bar_S) ||pi_(U_n)(s)-1||_2 -> 0
```

and the raw word at normalized-HS distance `sqrt(2)` from `1`.

Every word of `S_0` -- the 234 first-boundary words and the interior
separator `c_19243` -- lies in the normal closure of `bar_S`, so its defect
is at most a fixed multiple of `eps_n`; for the interior word this is exactly
`atlas-19243-centrality-is-bar-s-consequence`.  Hence

```text
sum_(s in S_0) ||pi_(U_n)(s)-1||_2^2 = O(eps_n^2) -> 0.
```

`atlas-linear-energy-controlled-by-full-packet-defect` then bounds the
linearized energy by `C'` times that, and
`atlas-boundary-tangent-covariance-coercivity` -- which holds for every
matrix at every multiplicity, not just infinitesimally -- gives

```text
a_n^2 + b_n^2 <= (1/14) sum_s l_s^2 <= (C'/14) * O(eps_n^2) -> 0.
```

That is (ASC).  Against `raw-swap-forces-two-s3-covariance-energy`, which
gives `a_n^2+b_n^2 >= 1/40-o(1)` on the same sequence, it is a
contradiction.  So `Q` is not hyperlinear, and it is explicit.

**Where the difficulty sits.**  In the first prerequisite alone; the other
five are established.  The route is deliberately narrower than
`two-s3-collapse-via-local-coercivity`: it asks for one inequality between
two finite energies rather than a metric localization statement, and it names
the packet -- boundary plus the interior separator -- for which the known
countermodel does not apply.
