---
rg: 2
id: finite-index-lifting-hosts-force-finite-stabilizers
kind: claim
title: A finite free host that lifts through a pmp action of its actor and has finite index over it forces that action to have finite stabilizers
distinct_from:
  free-actor-extensions-cannot-host-nonce-relation: that shows crossed products of the native free actor stay CE, an operator-algebra statement about one actor; this is a measure-theoretic obstruction for every actor, amenable or not, hyperlinear or not, and it uses no approximation property at all.
  finite-isotropy-relation-is-central-corner: that computes the corner when stabilizers are finite; this shows that finite stabilizers are forced whenever a lifting host has finite index, so infinite isotropy can only be hosted at infinite index.
  manzoor-isotropy-has-no-positive-finite-type-corner: that shows the native Manzoor stabilizers are infinite; this turns infinite stabilizers of any action containing the relation into a death step for every finite-index host lifting through that action.
artifacts:
  - research/finite-index-lifting-hosts-force-finite-stabilizers-proof.md
---

**ESTABLISHED** by `finite-index-lifting-hosts-force-finite-stabilizers-proof` (swarm-0917 w21, 2026-09-20, unreviewed).

**Setting.** `R` is a countable pmp Borel equivalence relation on a standard probability space `(X, mu)`. A
*free host* of `R` is the object of the same name in the w18 hosting claim (`nonce-relation-hosts-force-root-or-q1-failure`,
on the swarm branch):
* an essentially free action of a countable group `Lambda` on `(Z, zeta)` preserving a sigma-finite measure;
* a Borel set `A ⊆ Z` with `0 < zeta(A) < infinity`, and a Borel subrelation `S ⊆ R_Lambda(Z)|A`;
* a Borel map `r : A -> X` with `r_* zeta_A = mu` that maps a.e. `S`-class bijectively onto an `R`-class.

For `(a, a')` in `S` write `c(a, a')` for the unique `lambda` with `lambda a = a'`.

**Definitions.**
* The host *lifts through* a pmp action `Lambda ↷ (X, mu)` if `c(a, a') · r(a) = r(a')` for a.e. `(a, a')` in `S`.
  Then `R ⊆ R_Lambda(X)`. Every splitting host (item 2 of the hosting claim) and every host obtained by
  restricting a free extension `Z -> X` of an action that generates `R` lifts through that action.
* The *index* of the host at `z ∈ Lambda A` is `k(z) ∈ {1, 2, ..., infinity}`, the number of `S`-classes contained
  in `Lambda z ∩ A`. It is `Lambda`-invariant. `k ≡ 1` exactly when `S = R_Lambda(Z)|A`.
* The *Mackey mass* of the host is `M = ∫_(Lambda A) k d zeta ∈ (0, infinity]`.

## Statement

Let a free host of `R` lift through a pmp action `Lambda ↷ (X, mu)`.

1. **Finite hosts.** If `zeta(Z) < infinity`, then for `zeta`-a.e. `a ∈ A`: if `Stab_Lambda(r(a))` is infinite,
   then `k(a) = infinity`. In particular:
   * if the index is finite a.e., then `Stab_Lambda(x)` is finite for `mu`-a.e. `x`;
   * if `S = R_Lambda(Z)|A` (the full restriction), then `Stab_Lambda(x)` is finite for `mu`-a.e. `x`.
2. **Sigma-finite hosts.** If `M < infinity`, the same conclusion holds, even when `zeta(Z) = infinity`.
3. **Both hypotheses are needed.**
   * (Infinite index.) `Lambda = Z^2` acts on the circle `X` by `(m, n) x = x + m alpha`, with `alpha` irrational,
     so every stabilizer is `0 × Z`. It acts freely on the torus `Z = X × X` by `(x + m alpha, y + n beta)`. Take
     `A = Z`, let `S` be the orbits of `Z × 0`, and let `r(x, y) = x`. This is a finite host of the rotation relation
     that lifts through the action, with infinite stabilizers and `k ≡ infinity`.
   * (Infinite mass.) Let `Gamma ↷ (X, mu)` generate `R`, and let `nu` be an invariant random normalized
     transversal (the w18 normalized-section extension). The transversal space `{(x, T)}`, with
     `g(x, T) = (g x, T g^(-1))` and the sigma-finite measure induced from `nu`, is a free host restricted to
     `{1 ∈ T}`. Its host relation is the full restriction, so `k ≡ 1`.
     - The same `Z^2` rotation, with the deterministic transversal `T = Z × 0`, is a concrete instance. Its
       stabilizers are infinite, so part 1 forces `zeta(Z) = infinity`, hence `M = infinity`.
     - Proof step 5 gives this directly: no invariant probability exists on the transversal space.

## Consequences for the non-CE relations

* **Invariant.** The invariant is the *Mackey space* `Y` of the host. A point of `Y` is a point `z` of
  `Lambda A` together with one `S`-class inside `Lambda z ∩ A`, and `Y` carries the mass `M`. `Y` maps
  `Lambda`-equivariantly to `X`. `A` embeds in `Y` as a set that meets every orbit of every stabilizer
  `Stab_Lambda(x)`, acting on the fiber over `x`, in at most one point.
* **Death step.** An infinite group that preserves a finite fiber measure cannot have a positive-measure partial
  transversal.
* **What this kills.** Let `Gamma` act on `X` with `R ⊆ R_Gamma(X)` and with infinite stabilizers on a set of
  positive measure. Examples are the native free group of the Manzoor relation `R_mu`
  (`manzoor-isotropy-has-no-positive-finite-type-corner`) and the Kazhdan group `G ∈ WR(F_3, B)` generating the
  property-(T) relation `R_T`. Then no finite host of `R_mu` or `R_T` that lifts through `Gamma` has finite index
  on that set. Every *extension approach* dies at this step: take any free pmp extension `Z -> X` of `Gamma ↷ X`
  (Bernoulli, Gaussian, compact, coinduced, diagonal), restrict its orbit relation to a Borel set, and project.
  No choice of the extension or of the set helps.
* **Consequence.** A finite free host of `R_mu` is either non-lifting (its actor has no compatible pmp action on
  `X`), or lifts only at infinite index through an action with infinite isotropy, as in the torus example. A
  finite-index lifting host would force finite isotropy. That is exactly the regeneration hypothesis of item 3 of
  the hosting claim, weakened from generating `R` to containing `R`.
