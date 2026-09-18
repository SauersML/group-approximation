---
rg: 2
id: triangle-permutive-existence-iff-hex-cone-determinism
kind: claim
title: A free minimal triangle-permutive SFT exists iff some free minimal SFT is deterministic along three hexagonally alternating cones, and triangle-permutive SFTs have at most three one-sided nonexpansive lines
distinct_from:
  free-minimal-triangle-permutive-sft-exists: that is the existence problem for the triangle shape {0, e_1, e_2}; this proves it equivalent to the same problem for every three-cone determinism pattern (bipermutive cellular automata of any radius included), and proves the side-direction obstruction that node uses only heuristically.
  quantum-rigidity-passes-to-sub-sfts: that node's Remark conjectures that the nonexpansive directions of triangle-permutive SFTs are the three sides; Theorem B here proves it, with one-sidedness and conjugacy invariance.
  small-window-quasigroup-sub-sfts-have-periodic-points: that is an exhaustive search for small windows; this is a structural recoding theorem with no size bound.
---

**ESTABLISHED (proof in `triangle-permutive-existence-iff-hex-cone-determinism-proof`, unreviewed).**

**Definitions.** Let `S_1 = {(p,q) : q < 0, 0 <= p <= -q}`, `S_2 = {(p,q) : p < 0, 0 <= q <= -p}` and
`S_3 = {(p,q) : p, q >= 0} \ {0}`. These are three closed sectors, alternating with the three sectors of a hexagon.
A triple `(K_1, K_2, K_3)` of nonempty finite subsets of `Z^2 \ {0}` is **hex-alternate** if some real linear map
`A` has `A(K_j) ⊆ S_j` for `j = 1, 2, 3`. A `Z^2`-subshift `Ω` is **`(K_1,K_2,K_3)`-deterministic** if for each
`j` there is a function `f_j` with `x(z) = f_j(x|(z + K_j))` for all `x ∈ Ω` and `z ∈ Z^2`.

Triangle permutivity is the case `K_1 = {-e_2, e_1-e_2}`, `K_2 = {-e_1, -e_1+e_2}`, `K_3 = {e_1, e_2}`, `A = I`.

**Theorem A (recoding criterion).** The following are equivalent.
1. `free-minimal-triangle-permutive-sft-exists`: some finite quasigroup spacetime `X_⋆` contains a free minimal
   sub-SFT.
2. Some free minimal `Z^2`-SFT is `(K_1,K_2,K_3)`-deterministic for some hex-alternate triple.
3. For some `r >= 1`, finite alphabet `Σ` and bipermutive local rule `f : Σ^(r+1) -> Σ`, the spacetime
   `{x : x(z+e_2) = f(x(z), x(z+e_1), ..., x(z+r e_1))}` contains a free minimal sub-SFT.

In (2) ⇒ (1), a clopen piece of the higher-block recoding `y(u) = x|(A^(-1)u + B)` along the finite-index sublattice
`A^(-1)Z^2` is the triangle-permutive example, with `A` rational and `B` a large triangle.

**Theorem B (determining normals).** For a subshift `Ω` and a nonzero `n ∈ R^2`, say `n` is **determining** for
`Ω` if for every real `t`, any two points of `Ω` that agree on `{z : <z,n> < t}` are equal.
1. The property is invariant under conjugacy of `Z^2`-subshifts.
2. For every closed shift-invariant `Ω ⊆ X_⋆`, every `n` off the three rays `R_(>0)(1,1)`, `R_(>0)(0,-1)` and
   `R_(>0)(-1,0)` is determining. Moreover, if `n` and `-n` are both off these rays, the line `n^⊥` is expansive.
3. Consequently the nonexpansive lines of `Ω` are among the rows, the columns and the antidiagonal. On each of
   them at most one of the two normals is non-determining.
4. For a `(K_1,K_2,K_3)`-deterministic `Ω` with witness `A`, every normal off `A^T` of those three rays is
   determining.

**Corollary (obstruction).** Let `Ω` be a `Z^2`-subshift, `M : Z^2 -> Λ` an isomorphism onto a finite-index
subgroup, and suppose `(Ω, Λ)`, read through `M` as a `Z^2`-action, is conjugate to a closed invariant subset of
some `X_⋆`. Then the non-determining normals of `Ω` lie in the three rational rays `M^(-T)R_(>0)(1,1)`,
`M^(-T)R_(>0)(0,-1)` and `M^(-T)R_(>0)(-1,0)`. No two of these are antipodal, and `0` is interior to their convex
hull. For `M = I` (plain conjugacy) the rays are the three sides themselves. This excludes
every candidate with a two-sided fault, meaning two distinct points that agree on a half-plane together with two
distinct points that agree on the opposite half-plane of the same line. It also excludes every candidate with an
irrational non-determining normal, and every candidate with four non-determining rays.

**Effect on the target.** The search space of `free-minimal-triangle-permutive-sft-exists` widens from the single
triangle shape to all hex-alternate determinism patterns, including bipermutive automata of every radius. By
Theorem A that problem is unchanged. By Theorem B, any construction must have one-sided faults in at most three
rational directions. The Robinson-type item of that node's Attempts is excluded exactly when its faults are
two-sided in the sense above, which was not checked.
