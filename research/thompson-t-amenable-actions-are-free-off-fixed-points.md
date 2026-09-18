---
rg: 2
id: thompson-t-amenable-actions-are-free-off-fixed-points
kind: claim
title: Invariant means on Thompson T-sets are essentially free off the global fixed set, so every proper co-amenable subgroup of T makes T and F sofic
distinct_from:
  thompson-v-amenable-actions-are-free-off-fixed-points: that is the same statement for V, proved from the character simplex of V and prefix-code halving on the Cantor set; this is the circle group T, proved from Dudko--Medynets character rigidity for T and arc halving, with a self-contained derivation of IRS triviality from the character.
  no-proper-character-groups-avoid-amenable-orbit-full-groups: that imports "T has no proper characters" and excludes realizations of T in amenable orbit full groups; this turns the same rigidity into triviality of the stabilizer IRS of every invariant mean on every T-set.
  thompson-t-orbits-carry-no-invariant-means: that excludes invariant means on finite point sets of the circle, i.e. co-amenability of point and configuration stabilizers; this transfers the halving to every T-set whose stabilizers fix a finitely additive probability on dyadic arcs, and adds essential freeness and unconfinedness.
  elek-szabo-essentially-free-amenable-actions: that imports the general theory; this computes what simplicity and character rigidity force for T.
  mean-free-amenable-actions-residually-amenable-and-sofic: that proves heredity and soficity of mean-free amenable actions for all groups; this proves that for T every fixed-point-free invariant mean is mean-free, so co-amenability alone gives soficity.
  fg-amenable-subgroups-of-thompson-t-have-finite-orbits: that concerns amenable subgroups of T and their orbits on the circle; this concerns co-amenable subgroups and the invariant means on their coset spaces.
---

**ESTABLISHED.**

**Setting.**
- `T` is Thompson's group of piecewise-linear dyadic homeomorphisms of `S^1 = R/Z`. It is
  finitely generated, infinite and simple (classical, Cannon--Floyd--Parry, used as in
  `no-proper-character-groups-avoid-amenable-orbit-full-groups`, item 4). `S` is a finite
  symmetric generating set.
- `Ω` is a `T`-set and `m` a `T`-invariant mean on `ℓ∞(Ω)`. `Fix(g)` is the fixed set of `g`,
  `Fix(T) = ⋂_(s ∈ S) Fix(s)` is the set of global fixed points, and `Stab(x)` is the
  stabilizer of `x`. "Null" means `m`-null.
- `𝒜` is the algebra of finite unions of half-open arcs `[a,b)` of `S^1` with dyadic
  endpoints. It is `T`-invariant.
- A proper `H < T` is *confined by* a finite `P ⊆ T \ {e}` if every conjugate of `H` meets `P`.
- A *mean-free amenable action* is a `T`-set with an invariant mean giving `Fix(g)` mass `0`
  for all `g ≠ e`, as in `mean-free-amenable-actions-residually-amenable-and-sofic`. It is
  Elek--Szabó's essentially free amenable action.

**Statement.**
1. **Free off the fixed set.** For every `T`-set and every invariant mean,
   `m(Fix g) = m(Fix T)` for all `g ≠ e`.
   - The stabilizer IRS is `(1-b)δ_({e}) + bδ_T` with `b = m(Fix T)`.
   - If `b < 1`, the normalized restriction of `m` to `Ω \ Fix T` is mean-free.
2. **Reduction.** The following are equivalent, and each implies that `T` is sofic and that
   every subgroup of `T`, in particular `F`, is sofic.
   - (a) Some `T`-set without global fixed points carries an invariant mean.
   - (b) `T` has a mean-free amenable action.
   - (c) `inf { φ_S(T/H) : H < T proper } = 0`, where
     `φ_S(X) = inf_P Σ_(s ∈ S) |sP \ P| / |P|` over finite nonempty `P ⊆ X`.

   A proper co-amenable subgroup of `T` gives (a).
3. **Confining sets.** For every finite `P ⊆ T \ {e}`, `{x ∉ Fix T : Stab(x) ∩ P ≠ ∅}` is
   null. So no proper confined subgroup of `T` is co-amenable.
4. **Measure-fixing stabilizers.** `{x : Stab(x) fixes a finitely additive probability on 𝒜}`
   is null. So a co-amenable `H ≤ T` fixes no finitely additive probability on `𝒜`, and in
   particular:
   - no Borel probability on `S^1`;
   - no finite subset of `S^1`, which recovers (D1) of
     `thompson-t-co-amenable-subgroup-kills-real-euler-class`;
   - `H` is not amenable, since an amenable group of homeomorphisms of the compact space `S^1`
     fixes a Borel probability.

**Consequences.**
- **Barrier for the discrete Euler route.** `thompson-t-co-amenable-subgroup-kills-real-euler-class`
  needs a *proper* `H`, since `T̄` is perfect. By item 2, any witness makes `T` sofic and hence
  `F` sofic (routes `thompson-t-fixed-point-free-amenable-action-from-euler-subgroup`,
  `thompson-t-sofic-from-fixed-point-free-amenable-action`, `thompson-f-sofic-from-t-sofic`).
  So that route to `lifted-thompson-t-is-a-t-menable` is at least as hard as the open problem
  `thompson-f-is-sofic`. It is not killed.
- **Forced shape of a witness.** A co-amenable `H` in the Euler route must satisfy all of the
  following:
  - `T/H` with its mean is essentially free: for each fixed finite `P ⊆ T \ {e}`, almost every
    conjugate `tHt^(-1)` misses `P`;
  - `H` is not confined;
  - `H` fixes no finitely additive probability on dyadic arcs.
- **Test for future candidates.** Let `H < T` be proper. By item 1, `T/H` carries an invariant
  mean exactly when the action on `T/H` is essentially free amenable. So by Elek--Szabó
  Theorem 3 (verbatim in `elek-szabo-essentially-free-amenable-actions`), `H` fails to be
  co-amenable exactly when `T/H = A_1 ∪ ... ∪ A_l ∪ Fix(p_1) ∪ ... ∪ Fix(p_k)`, where the
  `p_i` are elements of `T` and there are `g_j, h_j` with `g_1A_1, h_1A_1, ..., g_lA_l, h_lA_l`
  pairwise disjoint. That is a paradoxical decomposition modulo finitely many fixed sets. It is
  easier to find than an honest one, and for `T/H` it is equivalent to one.

**Scope.** Items 1 and 3 are the finitely additive, `T`-specific analogue of known IRS rigidity
arguments from character rigidity. Item 4 is the standard halving computation, transferred.
No novelty is claimed for the method. The claim leaves `thompson-t-is-sofic` and
`thompson-t-has-a-fixed-point-free-amenable-action` OPEN. Means are only finitely additive, so
the unions of the null families above over all finite `P` are not controlled, and nothing here
refutes (a).

Proof route: `thompson-t-amenable-actions-free-off-fixed-points-proof`.
