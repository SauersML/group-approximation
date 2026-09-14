---
rg: 2
id: thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived
kind: claim
title: For every invariant mean on an F-set, the stabilizer IRS is a mixture of the trivial subgroup, with weight m(Moved(c)), and subgroups containing F'
distinct_from:
  thompson-f-following-models-separate-iff-mean-charges-commutator: that shows every nontrivial element of F' moves the same mean-mass t; this shows they all move the same set up to null sets, and that on it all of F acts mean-freely.
  thompson-f-interval-stabilizer-cosets-separate-only-if-amenable: that collapses separation on particular coset spaces to amenability; this constrains the stabilizers on every F-set at once.
  thompson-f-sofic-iff-relator-system-unstable: that makes soficity equivalent to separating almost-solutions; this makes following-model witnesses equivalent to mean-free amenable actions of F.
---

**ESTABLISHED.** **Setting.**
- `x_0, x_1` are the standard generators of `F`, composed right to left, and `c = x_0 x_1 x_0^-1 x_1^-1`.
- `F'` is the commutator subgroup.
- `Ω` is an `F`-set, and `m` is an invariant mean on `ℓ∞(Ω)`, as in
  `thompson-f-following-models-separate-iff-mean-charges-commutator`.
- `Fix(g)` and `Moved(g)` are the fixed and moved points of `g` in `Ω`. Put `X = Moved(c)` and
  `t = m(X)`.
- `Sub(F)` is the compact space of subgroups of `F`.
- The *stabilizer IRS* `μ_Ω` is the Borel probability measure on `Sub(F)` with
  `μ_Ω({H : Q ⊆ H, P ∩ H = ∅}) = m({ω : Q ⊆ Stab(ω), P ∩ Stab(ω) = ∅})` for finite `P, Q ⊆ F`.

**Statement.**
1. **One moved set.** `m(Moved(g) Δ X) = 0` for every `g ∈ F' \ {e}`.
2. **Almost invariance.** `m(gX Δ X) = 0` for every `g ∈ F`.
3. **Mean-freeness on X.** `m(X ∩ Fix(g)) = 0` for every `g ∈ F \ {e}`.
4. **Dichotomy.** `μ_Ω` is a conjugation-invariant probability measure, and
   `μ_Ω = t·δ_{e} + (1-t)·μ_0` with `μ_0` supported on subgroups that contain `F'`. In particular
   `t = μ_Ω({e})`.

**Corollaries.**
- **Witness form.** Say a *mean-free amenable action* of `F` is an `F`-set carrying an invariant mean
  with `m(Fix(g)) = 0` for all `g ≠ e`. A witness for `thompson-f-is-sofic` by permutation models that
  follow an `F`-set (with error `→ 0` and separation `≥ ε`) exists exactly when `F` admits a mean-free
  amenable action.
  - One direction: `m(Moved(c)) = 1`, then item 2 of
    `thompson-f-following-models-separate-iff-mean-charges-commutator`.
  - The other: normalize `m` on `X`, using items 2 and 3.
- **Where separation lives.** On any `F`-set, the separating part of an invariant mean sees only
  stabilizers that meet every finite subset of `F \ {e}` in the empty set, mean-almost surely. No
  positive-mass part sits over subgroups meeting `F'` nontrivially.
- **Single orbits.** A transitive `F`-set `F/H` carries a mean with `t > 0` only if `H` is co-amenable,
  and then its mean-generic points have stabilizers avoiding any given finite set. Truncations of
  non-amenable Schreier graphs keep the error bounded below by their Cheeger constants, so they never
  witness.

**Scope.** Elementary, and no novelty is claimed. It leaves `thompson-f-is-sofic` OPEN.
- **What it adds.** It turns the gap recorded in
  `research/artifacts/thompson-f-nonspatial-f-sets-2026-09-13.md` into one question: does `F` admit a
  mean-free amenable action?
- **Who has one.** Amenable groups do, through the regular action. Residually finite groups do, through
  limits of uniform measures on finite quotients. `F` has only abelian finite quotients, and it is LEA
  only if amenable (`thompson-f-is-lea-only-if-amenable`). So any mean-free amenable action of a
  non-amenable `F` must come from infinite orbits whose stabilizers shrink to `{e}`.
- **Candidate family.** An example is `k`-point configuration spaces with `k → ∞`, where the bound
  `4δ + k·sqrt(6δ)` of `thompson-f-spatial-permutation-models-almost-commute` degenerates.

Proof route: `thompson-f-mean-stabilizer-irs-dichotomy-proof`.
