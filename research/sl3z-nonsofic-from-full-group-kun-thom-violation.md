---
rg: 2
id: sl3z-nonsofic-from-full-group-kun-thom-violation
kind: route
title: A Kun-Thom pair acting inside the orbits of a free SL3(Z)-action with a non-invariant fixed algebra makes that action nonsofic
target: sl3z-admits-nonsofic-action
requires:
  - full-group-kazhdan-pairs-have-invariant-fixed-algebras
  - kun-thom-violation-inside-free-sl3z-orbit-relation
---

**Route.** Take the witness `(a, Γ ≤ H ≤ [R_a])` from `kun-thom-violation-inside-free-sl3z-orbit-relation`. If `a`
were sofic, `full-group-kazhdan-pairs-have-invariant-fixed-algebras` would force `L^∞^Γ` to be `H`-invariant. So `a`
is a nonsofic free action of `SL_3(Z)`.

**Direction.** Only this direction is known.

The converse would say: if `SL_3(Z) ∉ 𝒮`, a full-group Kun--Thom violation exists. It is open. The only known
obstruction to soficity of actions is Theorem 4.1, and this route is exactly that obstruction moved from subgroups
to full groups.

**Why this is not the dead Theorem C attempt.**

* Subgroups: `SL_3(Z)` has no infranormal non-normal Kazhdan pair. For mixing `a`, every infinite subgroup is
  ergodic (see the target's Attempts).
* Full groups: `[R_a]` contains torsion, non-linear and non-ergodic Kazhdan subgroups acting by piecewise
  `SL_3(Z)` elements. None of the no-go nodes addresses them.

## Seeds that die

* **N1: finite `Γ`-orbits.** This covers profinite seeds and `H` inside hyperfinite pieces. The fixed algebra is
  invariant unconditionally (proof node, Calibration C2). A witness needs `Γ` with infinite orbits on a
  non-invariant piece.
* **N2: homomorphic seeds.** Here `H` acts through a homomorphism `ρ : H → SL_3(Z)`, i.e. `c` is constant in `x`,
  so `b = a ∘ ρ`. Then `L^∞^Γ = L^∞^{ρΓ}`, and `(ρH, ρΓ)` is an infranormal Kazhdan pair in `SL_3(Z)`. If `ρΓ` is
  normal in `ρH` the fixed algebra is invariant, so a witness needs a non-normal such pair: the first bullet of the
  target's Attempts, where none is recorded (and one would already give a nonsofic action by
  `groups-containing-kun-thom-pair-have-nonsofic-actions`).
  * **Gap, cohomologous seeds.** For `c(h,x) = φ(b(h)x) ρ(h) φ(x)⁻¹` the map `Ψ(x) = φ(x)⁻¹·x` satisfies
    `Ψ ∘ b(h) = a(ρ(h)) ∘ Ψ`, is countable-to-one and has `Ψ_*μ ≪ μ`. Disintegrating `μ` over `Ψ` gives atomic
    fibre measures, so on each weight class `b` is a finite skew-product extension of `a ∘ ρ` on `(X, Ψ_*μ)`.
    Whether a non-invariant `L^∞^Γ` descends to `(ρH, ρΓ)` along such an extension is not proved here, so this
    case is not killed.
* **N3: untwistable cocycles with an ergodic torsion abelian subgroup.** Suppose `c` untwists to `ρ`, and `H`
  contains an infinite abelian torsion subgroup `L` acting ergodically on `X`. No witness exists.
  1. `ρ(L)` is a torsion abelian subgroup of `SL_3(Z)`, so it is finite.
  2. The finite set `ρ(L)Ψ(x)` is `L`-invariant, hence constant.
  3. So `Ψ` is finitely valued and `Ψ_*μ` is atomic.
  4. But `Ψ` is countably piecewise measure-preserving, so `Ψ_*μ ≪ μ`, which is nonatomic. Contradiction.
  5. Popa's cocycle superrigidity for malleable actions of groups with a w-normal relative-(T) subgroup applies
     to generalized Bernoulli actions `K^{H/Γ}` of the Kun--Thom groups of Theorem E (compare the established
     `kun-thom-relation-hosts-contain-sl-d-z-and-root-groups`, which already excludes every linear host for them), provided some elementary
     root subgroup `e_{ij}(R)` has infinite orbits on `H/Γ`. So N3 kills them, including the Corollary D seeds.
     This is sketch level: the w-normality and weak-mixing hypotheses are asserted, not written out.
* **What survives.** Kazhdan pairs acting by non-constant piecewise `SL_3(Z)` elements through a cocycle that is not
  constant (the cohomologous case is the N2 gap; N3 kills it when an ergodic infinite torsion abelian subgroup exists). These are non-malleable, non-Bernoulli `b`, e.g. algebraic or co-induced
  actions, or `b` in which every torsion abelian subgroup has non-ergodic, or finite-orbit, pieces.
