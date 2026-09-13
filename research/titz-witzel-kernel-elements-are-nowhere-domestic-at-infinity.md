---
rg: 2
id: titz-witzel-kernel-elements-are-nowhere-domestic-at-infinity
kind: claim
title: No nontrivial element of a Titz Mite--Witzel kernel maps an open set of chambers at infinity to non-opposite chambers
distinct_from:
  titz-witzel-kernels-are-mif: that asks mixed-identity-freeness of the kernels; this is a rank-two replacement for topological freeness on the chambers at infinity, one of the inputs of the ping-pong route to it.
---

**OPEN.** Let `Γ̌ = Γ̌_i^q` act on the exotic `C̃₂` building `X = X_i^q`, as in
`titz-witzel-simple-kazhdan-cat0-lattices-exist`. For every `g ∈ Γ̌ ∖ {1}`,
the closed set

```text
N(g) = {c ∈ Ch(∂X) : g·c is not opposite c}
```

has empty interior in the cone topology.

**Why it matters.** It is hypothesis (D1) of
`opposition-general-position-from-nowhere-domestic-dense-poles`, used in
`titz-witzel-kernel-mif-via-opposition-ping-pong`.

## Attempts

1. **Necessary for the route.** Hypothesis (GP) with `s = t` asks each constant
   to map a pole to an opposite chamber. So an element with `N(g) = Ch(∂X)`
   defeats the ping-pong for words such as `g·x·g'·x⁻¹`.
2. **Not a formal property of quadrangles.** Neyt--Parkinson--Van Maldeghem,
   arXiv:2403.17443v1, Theorem 1(1)(a) and Table 1 (pinned in the lane
   artifact): a collineation of a generalised quadrangle fixing an ovoid or a
   spread elementwise is uniclass, with displacement set `Cl(s_i)`. In the
   dihedral group of order 8 that class consists of reflections, and the
   longest element is not a reflection. So such a collineation maps no chamber
   to an opposite one. The claim has to use that `g` is a lattice element of
   the Euclidean building.
   - **The elements in question.** `Γ̌` is torsion-free and acts cocompactly,
     so every `g ≠ 1` is hyperbolic (semisimplicity of cocompact actions,
     Bridson--Haefliger II.6.10; not re-read).
3. **Product-of-trees analogue.** On `T₁ × T₂`, chambers at infinity are pairs
   of ends, opposite exactly when both coordinates differ. So `N(g)` has empty
   interior exactly when each coordinate of `g` has fixed-point sets with empty
   interior on its tree boundary, i.e. topological freeness on each factor.
   BFFHZ Remark 3.5 proves topological freeness on a tree boundary for
   Burger--Mozes groups (per a web summary of arXiv:2503.21882v2, not read at
   source).
4. **Simplicity doesn't obviously help.** Rybak's Kac--Moody argument turns a
   failure of topological freeness into rigid stabilizers with large direct
   sums. `N(g)` is not a fixed-point set, and the set
   `{g : int N(g) ≠ ∅}` is only known to be closed under inverses and
   conjugation, since `N(g⁻¹) = g·N(g)` and `N(ugu⁻¹) = u·N(g)`.
