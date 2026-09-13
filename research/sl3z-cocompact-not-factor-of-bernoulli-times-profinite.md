---
rg: 2
id: sl3z-cocompact-not-factor-of-bernoulli-times-profinite
kind: claim
title: SL3(Z) on SL3(R)/Λ, Λ from a cubic division algebra, is not a factor of Bernoulli times any free ergodic profinite action
distinct_from:
  sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions: that asks to exclude factors of Loeb ultraproducts of finite actions; this excludes the separable models, Bernoulli shifts times genuine profinite actions, through cocycle superrigidity
  sl3z-cocompact-quotient-uniformly-far-from-finite-actions: that excludes finite actions with every pair good, by holonomy and norm drift; this excludes measurable equivariant maps from Bernoulli times profinite actions, by Popa and Ioana untwisting followed by properness
---

**ESTABLISHED (unreviewed).** Let `Γ = SL_3(Z)` and let `Λ <= SL_3(R)` satisfy hypothesis (R) of
`sl3z-cocompact-quotient-uniformly-far-from-finite-actions`: `Λ` is a cocompact lattice with a faithful
`ι : Λ → GL_m(Q)` whose image has no nontrivial unipotent. Put `X = SL_3(R)/Λ`. Let `s` be the Bernoulli
action on `([0,1], Leb)^Γ` and `p` any free ergodic profinite action of `Γ`, for instance on the
profinite completion `SL_3(Ẑ)`. Then there is no measurable map `Ψ : s × p → X` with
`Ψ(γz) = γΨ(z)` for all `γ` and almost every `z`.

**Corollaries.**
1. `X` is not a factor of `s`, of `p`, of `s × p`, or of `s × p × ι` with `ι` trivial. Precompose with a
   projection, or restrict to almost every slice of the trivial factor. No measure condition is needed:
   by `sl3z-cocompact-quotient-uniquely-ergodic-minimal` any equivariant map pushes forward to Haar.
2. The same holds with `s × p` replaced by any action whose `Λ`-valued cocycles are virtually
   cohomologous to homomorphisms on finite-index subgroups.

**Calibration (correction, 2026-09-13): this theorem does not separate `Λ` from `SL_3(Z)`.** The first
version of this node called the theorem "the separable half" of the weak-containment exclusion. That
framing is wrong. The same untwisting applies to `SL_3(Z) ↷ SL_3(R)/SL_3(Z)` with Haar measure.
* The untwisted holonomy `ρ : Γ_a → SL_3(Z)` may have finite image. Then step 8 of the proof gives a
  contradiction.
* Otherwise, by Margulis superrigidity, `ρ` virtually extends to an automorphism `θ` of `SL_3(R)`. The
  lifted map is then equivariant for the twisted conjugation `x ↦ δxθ(δ)^(−1)` of a Zariski-dense `Γ_1`.
  By Borel density, invariant probability measures of that action sit on its fixed points. So the map is
  essentially constant and cannot be a factor map onto Haar measure.

This is a sketch: Margulis superrigidity and Borel density are not imported here. The Hecke action *is*
weakly contained in finite actions, through its finite Hecke orbits. So Bernoulli-times-profinite models
are already too small for an action that is weakly contained. (R) enters the proof only as a cheap
replacement for superrigidity. The theorem calibrates the tools. It excludes nothing that separates
commensurability classes, and the whole weak-containment question lives in the ultraproducts. (`s ≺ p`
by Abért--Weiss, recalled and not imported, and `p` is weakly contained in finite actions. By equivalent
form 2 of `sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions`, weak containment means being
a factor of a Loeb ultraproduct of finite actions.)

**Where the argument stops.** Ioana's proof zooms in at a finite level `n` where the cocycle is almost
constant on fibres of `r_n`. In an ultraproduct of finite actions the relevant level is nonstandard, with
point stabilizers that are internal congruence subgroups `Γ(N_k)`. Untwisting there holds only on most
fibres, so it returns a `Λ`-valued almost-cocycle with a vanishing fraction of defects, which is the
problem again.

**Credit (ex-verify2-dynamics, 2026-09-13).** The untwisting in steps 2–3 of the proof, a cocycle of profinite
times Bernoulli cohomologous to one over a finite level of the profinite factor, is already stated by Ioana.
- *Source.* arXiv:0805.2998v1, §3, Remark (2): "let w : Γ × (X × Y) → Λ be a cocycle for the diagonal product action
  α × ρ ... Then there exist n such that w is cohomologous to a cocycle w′ ... of the form w′ = w′′∘(id × s_n)".
- *What is new here.* Steps 4–8: killing the holonomy under (R) through Bass–Milnor–Serre and almost-simplicity, and
  then properness.
- *Review.* `research/artifacts/ex-review2-dynamics-2026-09-13-part7.md`, §7.2 (PASS).

Proof in `sl3z-cocompact-not-factor-of-bernoulli-times-profinite-proof`.
