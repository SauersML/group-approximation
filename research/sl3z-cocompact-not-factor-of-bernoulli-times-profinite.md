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

**Calibration.**
* `Λ = SL_3(Z)` fails (R). There the untwisted holonomy may be the identity embedding of a congruence
  subgroup, and properness gives nothing: the argument uses (R) exactly once.
* Weak containment. `s ≺ p` (Abért--Weiss: Bernoulli shifts are weakly contained in every free action;
  recalled, not imported), and `p` is weakly contained in finite actions. By equivalent
  form 2 of `sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions`, weak containment of `X` in
  finite actions means that `X` is a factor of a Loeb ultraproduct of finite actions. This theorem is
  therefore the separable half of that exclusion. It excludes every model in which the approximating
  finite actions sit inside one fixed profinite action, possibly after a Bernoulli product.

**Where the argument stops.** Ioana's proof zooms in at a finite level `n` where the cocycle is almost
constant on fibres of `r_n`. In an ultraproduct of finite actions the relevant level is nonstandard, with
point stabilizers that are internal congruence subgroups `Γ(N_k)`. Untwisting there holds only on most
fibres, so it returns a `Λ`-valued almost-cocycle with a vanishing fraction of defects, which is the
problem again.

Proof in `sl3z-cocompact-not-factor-of-bernoulli-times-profinite-proof`.
