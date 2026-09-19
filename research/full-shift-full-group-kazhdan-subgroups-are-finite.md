---
rg: 2
id: full-shift-full-group-kazhdan-subgroups-are-finite
kind: claim
title: "Every Kazhdan subgroup of the topological full group of the two-sided full shift is finite, with orbit sizes on aperiodic points at most 1 + 8r/ε²"
distinct_from:
  dense-finite-free-orbits-force-finite-kazhdan-subgroups: that assumes the finite orbits through free points are dense and then bounds them by closedness, for acting groups A × F_d; this proves, for the full shift, that every aperiodic orbit of a Kazhdan subgroup is finite and of explicitly bounded size, by a one-dimensional Cheeger cut, and needs no density hypothesis
  subexponential-schreier-growth-excludes-sl3z-and-bs1k: that excludes SL_3(Z), BS(1,k) and H_3(Z) from the full-shift host by counting Schreier balls; this excludes every infinite Kazhdan group, by an isoperimetric bound instead of a distortion bound
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that is the open question for all of nV; this settles it for the copy of [[X]] inside the measure-preserving subgroup M_2 of 2V, and records that the argument dies on M_2 itself, whose orbits grow exponentially
  full-shift-topological-full-group-is-residually-finite: that gives finite quotients of [[X]] from periodic points; this uses aperiodic points and property (T), and bounds orbit sizes
---

**ESTABLISHED** by `full-shift-full-group-kazhdan-finite-proof`.

## Setting

`X = {0,1}^Z` with shift `σ(x)_i = x_{i+1}`. `[[X]]` is the group of homeomorphisms `f` of `X`
with `f(x) = σ^{k_f(x)} x` for a continuous `k_f: X → Z`. A point `x` is *aperiodic* if
`σ^j x ≠ x` for all `j ≠ 0`.

## Statement

Let `Γ ≤ [[X]]` have Kazhdan's property (T). Let `(S, ε)` be a Kazhdan pair for `Γ`, and let
`r = max_{s ∈ S} max_x |k_s(x)|`.

1. Every `Γ`-orbit of an aperiodic point is finite, of size at most `1 + 8r/ε²`.
2. `Γ` is finite.

The same holds for the image of any homomorphism from a Kazhdan group into `[[X]]`.

## Remarks

- **Prior art.** This is in the spirit of Juschenko and de la Salle, *Invariant means for the
  wobbling group* (arXiv:1301.4736). As recalled, and not checked verbatim, they show that Kazhdan
  subgroups of wobbling groups of spaces of subexponential growth are finite. No priority is
  claimed. The route is self-contained.
- **Where it sits.** By `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, item 3(c),
  `Φ^{-1} [[X]] Φ` is a subgroup of the measure-preserving subgroup `M_2 ≤ 2V`. So the part of
  `kazhdan-subgroups-of-brin-thompson-groups-are-finite` that lives in this copy of `[[X]]` is
  settled.
- **Where the argument dies.** The proof uses that each orbit is a subset of one line `Z` on which
  generators move points a bounded distance, so half-lines are Cheeger cuts of bounded boundary.
  In `M_2` a generator may also rewrite finitely many coordinates, and orbits of the
  homoclinic-plus-shift groupoid grow exponentially. There the half-line cut has no analogue.
