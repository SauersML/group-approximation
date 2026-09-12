---
rg: 2
id: ssa-unit-divisibility-uhf-absorption-proof
kind: route
title: Realize a matrix unit from class arithmetic and push it down the tensor tail
target: ssa-unit-divisibility-forces-uhf-absorption
requires: []
---

**Unital `M_p` from divisibility.**  Write `[1] = p·x` in `K_0(D)`.
`D` is simple, nuclear (approximately inner flip; Effros--Rosenberg),
with the Toms--Winter dichotomy: stably finite with unique trace, or
purely infinite.  Finite case: `D` is `Z`-stable (Winter), hence of
stable rank one (Rordam), hence has cancellation; `x` is realized by a
projection `q` in a matrix algebra with `q^{⊕p} ~ 1`, giving a unital
`*`-homomorphism `M_p → D`.  Purely infinite case: `x = [q]` for a
full properly infinite projection `q` (Cuntz), `q^{⊕p}` is full
properly infinite of class `[1]`, and Cuntz's theorem (properly
infinite full projections with equal class are equivalent) again gives
`q^{⊕p} ~ 1` and a unital `M_p → D`.

**Tensor-shift centrality.**  Iterating strong self-absorption gives
`D ≅ D^{⊗∞}`.  For `b ∈ N` let `σ_b : D^{⊗∞} → D^{⊗∞}` be the unital
endomorphism `y ↦ 1^{⊗b} ⊗ y`.  Given the unital copy
`M_p ⊆ D` and a finite subset `F` of `D`, approximate `F` inside the
first `m` tensor factors and place `σ_{m}(M_p)`: it commutes exactly
with the approximants.  Choosing `b_i → ∞` along the ultrafilter
produces a unital `M_p → D_ω ∩ D'`.  Iterating (separability, the
standard Effros--Rosenberg/McDuff criterion for UHF absorption) gives
`D ≅ D ⊗ M_{p^∞}`; running over `p ∈ J` with an intertwined diagonal
sequence gives `D ≅ D ⊗ M_{J^∞}`.

**Central upgrade for an arbitrary SSA target `E`.**  Fix
`E ≅ E^{⊗∞}` and let `σ_b` be its block shifts.  For
`s = (s_i) ∈ E_ω` set `Φ(s) := (σ_{b_i}(s_i))` with `b_i → ∞`:
`Φ` is well defined (each `σ_b` is isometric), unital, multiplicative
(each `σ_b` is a `*`-homomorphism applied entrywise), and its image
commutes with every fixed `e ∈ E` supported in finitely many tensor
factors, hence with all of `E`.  So `Φ : E_ω → E_ω ∩ E'` is a unital
`*`-homomorphism, and any unital `D → E_ω` composes to
`D → E_ω ∩ E'`; the McDuff-type criterion for the strongly
self-absorbing `D` then gives `E ≅ E ⊗ D`.

**Guard (why nothing stronger follows).**  A unital `O_2 ⊆ D` needs
`[1_D] = 0` (the unit class is the image of `[1_{O_2}] = 0`), which is
exactly why the argument yields `M_p`'s from divisibility but no more;
e.g. `O_2 ⊄ O_∞` unitally since `[1_{O_∞}] = 1 ≠ 0`.
