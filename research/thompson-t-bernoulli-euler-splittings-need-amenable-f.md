---
rg: 2
id: thompson-t-bernoulli-euler-splittings-need-amenable-f
kind: claim
title: "If Thompson's F is nonamenable, no Bernoulli or Gaussian Thompson T-space (generalized, with amenable F-stabilizers and infinite local orbits) carries a measurable Euler splitting; so every probability-measure witness for (MT) of that shape needs F amenable"
distinct_from:
  thompson-t-euler-class-splits-over-almost-invariant-space: that is the open existence statement (MT); this kills the Bernoulli and Gaussian probability-measure witnesses for it, conditional on non-amenability of F
  perfect-extension-splittings-are-not-uniformly-integrable: that kills uniformly integrable splittings over any space and all splittings over spaces fibred over S^1; this kills arbitrary (heavy-tailed, L^0) splittings, but only over Bernoulli and Gaussian spaces and only if F is nonamenable
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that is the counting-measure case X = T/H; this is the opposite regime (probability measures, mixing), and its Bernoulli spaces over T/H cover H = PSL_2(Z)
  sp4-maslov-circle-survives-in-bernoulli-l0-cohomology: that uses property (T) of Sp_4(Z) through Jiang's lemma; T is Haagerup, and here the rigidity comes instead from Popa's spectral-gap theorem on the commuting pair F_A x F_B
artifacts: []
---

**ESTABLISHED** (the implication, conditional on its hypothesis) by
`thompson-t-bernoulli-euler-splittings-need-amenable-f-proof`.

## Notation

- `T̄` is the lift of `T` to `R`, `π : T̄ → T`, `z` is translation by `1`, and `ker π = ⟨z⟩`.
- For a closed dyadic arc `J ⊊ S^1` with nonempty interior, `F_J = {f ∈ T : f = id off J}`.
  Put `B = [0, 1/2]` and `A = [1/2, 1]`. Then `F_A` and `F_B` are copies of `F` that commute.

## Statement

Assume **`F` is nonamenable**. Let `(X, μ)` be a standard probability space with a
measure-preserving action of `T`, so that `T̄` acts through `π`. Assume one of the following.

- **(Ber)** `X = (X_0, μ_0)^I` is the generalized Bernoulli action over a countable `T`-set `I`,
  with any standard base (atoms allowed, base not a single point), such that:
  - `Stab_{F_A}(i)` is amenable for every `i ∈ I`;
  - every `F_J`-orbit in `I` is infinite, for every dyadic arc `J` with nonempty interior.
- **(Gau)** `X` is the Gaussian action of an orthogonal representation `ρ` of `T` such that:
  - `ρ|_{F_A}` has stable spectral gap, meaning `ρ ⊗ ρ̄` restricted to `F_A` has no almost
    invariant vectors;
  - `ρ|_{F_J}` has no nonzero finite-dimensional invariant subspace, for every dyadic arc `J`
    with nonempty interior.

Then:
1. For every `θ ∈ R \ Z` there is no measurable cocycle `w : T̄ × X → S^1` with
   `w(z, ·) = e^{2πiθ}` a.e.
2. In particular, there is no measurable Euler splitting over `X`. That is, there is no
   measurable `β : T̄ × X → R` with `β(gh, x) = β(g, hx) + β(h, x)` and `β(z, ·) = 1` a.e.
   Equivalently, `e_R` survives in `H²(T; L⁰(X, R))`.

**Examples of (Ber).**
- `I = T` acting on itself by left translation, giving the usual Bernoulli shift `X_0^T`. All
  stabilizers are trivial.
- `I = T/K`, provided that for every `t ∈ T`:
  - `F_A ∩ tKt^{-1}` is amenable;
  - `F_J ∩ tKt^{-1}` has infinite index in `F_J`, for every dyadic `J`. This is what makes the
    `F_J`-orbit of `tK` infinite.
- `K = PSL_2(Z)` satisfies both, for the following reasons.
  - `F_J ≅ F` is torsion-free and has no nonabelian free subgroup (Brin–Squier). So its
    intersection with the virtually free group `tKt^{-1}` is torsion-free and virtually free
    with no `F_2`, hence cyclic or trivial.
  - A finite-index subgroup of `F_J` contains `Z²`, so it is not cyclic.

## Role

- The hypothesis is the open claim `thompson-f-is-not-amenable`. If that claim is established,
  the conclusion becomes unconditional.

- By `central-extension-haagerup-from-measurable-euler-splitting`, every probability-measure
  `T`-space is a candidate witness for (MT). The Koopman condition is automatic, because the
  constant function `1` is invariant. So for probability spaces, (MT) asks exactly for a pmp `X`
  with `e_R ↦ 0` in `H²(T; L⁰(X, R))`.
  - For amenable groups this is easy: every class dies over a free ergodic pmp action, by
    Connes–Feldman–Weiss orbit equivalence to `Z`.
  - Bernoulli shifts are the standard source of flexible `L⁰` cohomology. This claim says they
    are useless for `T` unless `F` is amenable.
- *Obstruction class killed (type 3).* The killed class is every pmp witness whose restriction
  to `F_A × F_B` is a Bernoulli or Gaussian action with the stated spectral conditions.
  - *Invariant:* the untwisting of `S^1`-valued cocycles on the commuting pair `F_A × F_B`,
    by Popa's spectral-gap superrigidity.
  - *Step where every member dies:* the untwisting propagates along the relation "the arcs
    `B` and `gB` overlap", which generates `T̄` and also contains `z`. Perfectness of `T̄` then
    forces `e^{2πiθ} = 1`.
- *Dichotomy.* Either `F` is amenable, or (MT) must be witnessed over a space that is neither
  Bernoulli nor Gaussian in this sense (or over an infinite measure). The latter includes the
  discrete co-amenable route `thompson-t-co-amenable-subgroup-kills-real-euler-class`, which
  this claim does not touch.

## Attempts

- 2026-09-18 (swarm-0917-w11-w11-nv-pull): proved. Popa (JAMS 2008) Theorem 1.1 and
  Corollary 1.2 were read in the arXiv source math/0608429.
  - An unconditional version is blocked because it needs infinite commuting subgroups `H, H'`
    of `T` with `H` nonamenable. Sketch, not proved: if `H` commutes with an infinite `H'`,
    then `H` virtually fixes a point of `S^1`, so it is virtually a subgroup of a point
    stabilizer. Point stabilizers are amenable if `F` is.
  - So Popa's product method cannot be run on `T` without deciding the amenability of `F`.
