---
rg: 2
id: thompson-v-amenable-actions-are-free-off-fixed-points
kind: claim
title: Invariant means on Thompson V-sets are essentially free off the global fixed set, and their stabilizers avoid measure-fixing subgroups, rigid covers and each confining set
distinct_from:
  thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived: that decides the stabilizer IRS of invariant means for Thompson's F, where the answer may contain F'; this shows that for the simple group V the stabilizer IRS is always a mixture of the trivial and full subgroups, and adds exclusions coming from the Cantor action.
  thompson-f-mean-free-actions-dense-configurations-or-unconfined: that keeps dense finite configurations in (0,1) as a surviving witness shape for F; for V the halving obstruction kills configurations of every size, together with every proper subgroup containing a rigid cover.
  almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial: that concerns finite permutation almost actions and their Hamming limits; this concerns finitely additive invariant means on arbitrary V-sets and the stabilizers they charge.
  stabilizer-rigid-groups-avoid-amenable-orbit-full-groups: that excludes nontrivial realizations of V inside measure-preserving amenable orbit full groups; this constrains the point stabilizers of V-sets carrying invariant means.
  elek-szabo-essentially-free-amenable-actions: that imports the general theory and the obstruction subgroup; this computes what simplicity and character rigidity force for V.
  mean-free-amenable-actions-residually-amenable-and-sofic: that proves existence for residually amenable groups, heredity, soficity and nullity of amenable stabilizers for all groups; this proves V-specific nullity for stabilizers fixing a Borel probability on the Cantor set, for rigid covers and for each confining set.
  thompson-v-cantor-orbits-have-no-folner-sets: that rules out almost-invariant finite subsets of the Cantor set itself; this transfers the same halving to every V-set whose stabilizers fix a probability on the Cantor set, and to rigid covers.
artifacts:
  - research/artifacts/thompson-v-amenable-actions-2026-09-16.md
---

**ESTABLISHED.**

**Setting.**
- `V = G_(2,1)` acts on `C = {0,1}^N`. `[w]` is the cone of sequences with prefix `w`.
- For a clopen `U`, the *rigid stabilizer* `V_U` is the set of elements that fix every point outside `U`.
- `S` is a finite symmetric generating set of `V`.
- `Ω` is a `V`-set and `m` an invariant mean on `ℓ∞(Ω)`. `Fix(g)` is the fixed set of `g`,
  `Fix(V) = ⋂_(s ∈ S) Fix(s)`, and `Stab(x)` is the stabilizer of `x`. "Null" means `m`-null.
- `φ_S(X) = inf_P Σ_(s ∈ S) |sP \ P| / |P|` over finite nonempty `P ⊆ X`.
- A proper `H < V` is *confined by* a finite `P ⊆ V \ {e}` if every conjugate of `H` meets `P`.
- `𝓜` is the family of subgroups of `V` that fix a Borel probability measure on `C`.
- `𝓒` is the family of proper subgroups of `V` that contain `V_(U_1), ..., V_(U_k)` for some finite
  clopen partition `{U_i}` of `C`.

**Statement.**
1. **Reduction.** The following are equivalent, and each implies that `V` is sofic.
   - (a) Some `V`-set without global fixed points carries an invariant mean.
   - (b) `V` has an essentially free amenable action (Elek–Szabó, Definition 1.3).
   - (c) `inf { φ_S(V/H) : H < V proper } = 0`.
   - (d) `N_V ≠ V`, where `N_V` is the characteristic subgroup of Elek–Szabó §5.

   A proper co-amenable subgroup of `V` gives (a).
2. **Free off the fixed set.** For every `V`-set and every invariant mean, `m(Fix g) = m(Fix V)` for all
   `g ≠ e`.
   - The stabilizer IRS is `(1-b)δ_({e}) + bδ_V` with `b = m(Fix V)`.
   - If `b < 1`, the normalized restriction of `m` to `Ω \ Fix V` is essentially free.
3. **Confining sets.** For every finite `P ⊆ V \ {e}`, `{x ∉ Fix V : Stab(x) ∩ P ≠ ∅}` is null. In
   particular no proper confined subgroup of `V` is co-amenable.
4. **Measure-fixing stabilizers.** `{x : Stab(x) ∈ 𝓜}` is null. This family contains:
   - the amenable subgroups;
   - the subgroups with a finite orbit on `C`, among them point stabilizers, stabilizers of finite
     configurations, and `F`;
   - the subgroups preserving the Bernoulli measure.

   More generally (transfer), let `Y` be a `V`-set and `𝒜` a `V`-invariant algebra on `Y` carrying no
   invariant finitely additive probability. Then the stabilizers that fix a finitely additive probability
   on `𝒜` are null.
5. **Rigid covers.** `{x : Stab(x) ∈ 𝓒}` is null. It contains setwise stabilizers of proper nonempty
   clopen sets and stabilizers of finite clopen partitions with at least two pieces.
6. **Uniform isoperimetric bounds.** There are constants `c > 0`, and `c_P > 0` for each finite
   `P ⊆ V \ {e}`, with the following property. Let `H < V` be proper and let `H ≤ K`, where `K` is in
   `𝓜 ∪ 𝓒` or `K` is proper and confined by `P`. Then `φ_S(V/H) ≥ c`, respectively `≥ c_P`.
7. **Density.** Let `x ↦ K(x) ⊆ C` satisfy `K(gx) = gK(x)`. For every proper clopen `U`,
   `{x : ∅ ≠ K(x) ⊆ U}` is null. Consequences:
   - For each `n`, almost every `x ∉ Fix V` has no cone of length `≤ n` inside
     `O(x) = ⋃{U : V_U ≤ Stab(x)}`.
   - `{x : the Stab(x)-invariant clopen algebra is finite with at least two atoms}` is null.

**Consequences.**
- **Shape of a witness for (a).** Typical stabilizers of a witness are proper and wq*-normal. The
  wq*-normality is imported from Tucker-Drob, arXiv:1407.7474v3, Theorem 1. It is not part of items 1–7
  and nothing above depends on it. Items 3–7 then force them to satisfy the following. Each statement is
  "almost every stabilizer", for one fixed family at a time.
  - For each fixed finite `P ⊆ V \ {e}`, almost every stabilizer misses `P`. This does not say that
    almost every stabilizer is trivial, because the union over all `P` is not controlled.
  - They are non-amenable, with no finite orbit on `C`.
  - They fix no Borel probability on `C`.
  - They lie in no member of `𝓒`. For a single orbit `Ω_0 = V·x_0` with `Stab(x_0) ≤ K ∈ 𝓒`, the map
    `g x_0 ↦ gK` into `V/K` is well defined and equivariant, and item 5 makes `V/K` null. Choosing one
    such `K` per orbit gives the same conclusion for the whole set.

  Since co-amenability passes to overgroups, the co-amenable candidates are the proper subgroups outside
  the downward closures of `𝓜`, `𝓒` and the confined subgroups.
- **Contrast with F.** For `F`, dense configurations in `(0,1)` survive as a witness shape. For `V`,
  finite configurations in `C` of every size are dead by item 4.
- **Open test case.** Thompson's `T ≤ V` is not in `𝓜`, contains no `V_U`, preserves no finite
  clopen partition, and lies below no member of `𝓒` (artifact §7). Whether `T` is confined, and whether
  `φ_S(V/T) = 0`, remain open.

**Scope.**
- Elementary given the imports `thompson-v-finitely-presented-infinite-simple`,
  `thompson-v-character-simplex` and `elek-szabo-essentially-free-amenable-actions`.
- Item 2 is the finitely additive, `V`-specific analogue of known IRS rigidity arguments. Items 1 and 3
  are close to folklore.
- This claim leaves `thompson-v-is-sofic` and `thompson-v-has-a-fixed-point-free-amenable-action` OPEN.
  It does not refute (a): means are only finitely additive, so the unions of the null families above
  over all confining sets, or over all scales, are not controlled.

Proof route: `thompson-v-amenable-actions-free-off-fixed-points-proof`.
