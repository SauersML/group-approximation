---
rg: 2
id: nonsofic-free-burnside-gives-nonsofic-hyperbolic-group
kind: claim
title: A nonsofic or non-hyperlinear free Burnside group of large odd exponent gives a hyperbolic group with the same defect
distinct_from:
  nonsofic-hyperbolic-group: that is the open existence question; this is the established implication from a negative answer to Weiss's Question 9.4, in the Coulon exponent range, to that existence
  local-approximation-properties-are-marked-closed: that is the general closedness theorem in the space of marked groups; this applies it to the Delzant--Gromov sequence converging to B(m,N)
---

**ESTABLISHED** through `nonsofic-free-burnside-gives-nonsofic-hyperbolic-group-proof`.

**Statement.** Take the following setup.
- `m >= 2`.
- `N` odd with `N >= n_1(F_m)`, the bound in
  `free-burnside-is-a-limit-of-hyperbolic-groups`.
- `P` is soficity, hyperlinearity, or any property `P_M` of
  `local-approximation-properties-are-marked-closed`.

If `B(m,N)` fails `P`, then some non-elementary hyperbolic group fails `P`.
Concretely, let `F_m = G_0 -> G_1 -> ...` be the Delzant--Gromov sequence of
that claim. Then `G_k` fails `P` for every sufficiently large `k`.

Contrapositive: if every hyperbolic group is sofic (or hyperlinear), then
`B(m,N)` is sofic (or hyperlinear) for every odd `N >= n_1(F_m)`.

**Consequence for Weiss's Question 9.4** (Pestov, arXiv:0804.3968v8, §9, "Is
the free Burnside group of a finite exponent n sofic?"). In this exponent range:
- A negative answer, by any method, gives a nonsofic hyperbolic group, so it
  answers `nonsofic-hyperbolic-group`.
- A non-hyperlinearity proof gives a non-hyperlinear hyperbolic group.

So the negative side of 9.4 is at least as hard as those problems.

**Scope.** The claim covers odd `N >= n_1(F_m)`, where `n_1` is the unspecified
threshold of Coulon's notes. Even exponents, and odd exponents below `n_1`, are
not covered: no limit-of-hyperbolic presentation for them was pinned. No
literature search for this implication was done, and no priority is claimed.
