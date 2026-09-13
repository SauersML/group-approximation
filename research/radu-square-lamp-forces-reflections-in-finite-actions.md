---
rg: 2
id: radu-square-lamp-forces-reflections-in-finite-actions
kind: claim
title: In every finite action of Radu's arithmetic quotient, a point fixed by a, b, cac, cbc is fixed by a reflection of the square, so the sign kernel is not closed
distinct_from:
  radu-delta-squared-orbit-is-signed-permutation-module: that proves a sign-reversing element of H_Q cap N kills the mark in a finite quotient, and leaves non-closedness of ker psi' as a hypothesis; this derives that hypothesis for every N from Radu's finite residual, and extends it to arbitrary finite Q-sets and colourings
  radu-horizontal-quotient-is-arithmetic-lattice: that identifies Q and its trees; this is a statement about all finite Q-sets, obtained from the non-residual finiteness of the lattice
artifacts:
  - research/artifacts/radu-edge-lamp-host-and-square-firewall-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Notation of `radu-metabelian-quotient-embeds-in-edge-lamp-wreath`:
`Q` is the arithmetic quotient, `C = <a,b,c>`, `C_χ = <a, b, cac, cbc>`, `D_4 = <x, c>`, and `ε` is the
orientation character of the square, with `ε(x) = ε(z) = ε(c) = −1`.

1. **Reflections.** Let `Q` act on a finite set `Ω`, and let `p ∈ Ω` be fixed by `a, b, cac, cbc`.
   Then one of the four reflections `x, z, c, xzc` of the square fixes `p`.
2. **Non-closedness.** For every finite-index normal subgroup `N ◁ Q`, the group
   `H_Q ∩ N` contains an element `h` with `ψ'(h) = −1`. Here `H_Q = <a,b,c,x,z>` and `ψ'` are as in
   `radu-delta-squared-orbit-is-signed-permutation-module`. So `ker ψ'` is not closed in the topology
   induced on `H_Q` by the profinite topology of `Q`, and the hypothesis of item 4 there holds.
3. **Colourings.** Let `ρ` be an action of `Q` on a finite set `A`, and let `f : A → B` satisfy
   `f∘ρ(h) = f` for `h ∈ {a, b, cac, cbc}`. Then `f∘ρ(g) = f` for some reflection `g ∈ D_4`.
   So no genuine finite action can be an orbit approximation of the coset action `Q ↷ Q/C_χ` with
   exactly invariant colouring (radius 3 already fails).

Items 1–3 are the finite-set shadow of the mark. Together with item 4 of
`radu-delta-squared-orbit-is-signed-permutation-module` they give an equivalence: `(xz)^4` lies in the
finite residual of `G_2` iff `ker ψ'` is not closed.

Item 3 is exact. Its approximate version, where the invariance defect is small instead of zero,
needs a uniform spectral gap of `C_χ` on all finite `Q`-sets (property τ plus the congruence subgroup
property for `Q`). Passing to sofic models needs flexible permutation stability of `Q`.

Proof in `radu-square-lamp-forces-reflections-in-finite-actions-proof`.
