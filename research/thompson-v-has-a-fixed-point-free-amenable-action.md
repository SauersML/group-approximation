---
rg: 2
id: thompson-v-has-a-fixed-point-free-amenable-action
kind: claim
title: Some Thompson V-set without global fixed points carries a V-invariant mean
distinct_from:
  thompson-v-is-sofic: that is soficity of V; this is one sufficient condition for it through amenable actions, and a refutation of this would say nothing against soficity.
  thompson-v-amenable-actions-are-free-off-fixed-points: that proves what every invariant mean on a V-set must look like and which stabilizer families are null; this asks whether any invariant mean off the global fixed set exists at all.
  elek-szabo-essentially-free-amenable-actions: that imports the general theory and the obstruction subgroup of an arbitrary group; this is the single instance that the obstruction subgroup of V is proper.
  mean-free-amenable-actions-residually-amenable-and-sofic: that constructs mean-free amenable actions for residually amenable groups; V is infinite and simple, so that construction gives nothing here.
  simple-kazhdan-groups-have-no-proper-co-amenable-subgroups: that excludes proper co-amenable subgroups when property (T) holds; V has the Haagerup property, so that argument is unavailable and the question is live.
  thompson-v-cantor-orbits-have-no-folner-sets: that rules out Følner sets on orbits of the natural Cantor action; this asks for almost-invariant finite sets on some coset space of V, necessarily with stabilizers far from those of the Cantor action.
artifacts:
  - research/artifacts/thompson-v-amenable-actions-2026-09-16.md
---

**OPEN.** Let `V = G_(2,1)` with finite symmetric generating set `S`. Prove that some `V`-set `Ω` with
no global fixed point carries a `V`-invariant mean on `ℓ∞(Ω)`.

**Equivalent forms.** By item 1 of `thompson-v-amenable-actions-are-free-off-fixed-points`, this claim
is equivalent to each of the following.
- `V` has an essentially free amenable action (Elek–Szabó, Definition 1.3).
- `inf { φ_S(V/H) : H < V proper } = 0`. Here `φ_S` is the isoperimetric constant of the Schreier
  graph, so this asks for almost-invariant finite sets on single coset spaces.
- The characteristic subgroup `N_V` of Elek–Szabó §5 is not `V`.

A proper co-amenable subgroup `H < V` would suffice, with `Ω = V/H`.

**Why it matters.** It implies `thompson-v-is-sofic` (route
`thompson-v-sofic-from-fixed-point-free-amenable-action`). The implication is one-directional. The
negation says exactly that `N_V = V`, and that is compatible with `V` being sofic.

## Attempts

- **2026-09-16, lane `thompson-v-is-sofic`.** Most natural witness families are dead, and the survivors
  are described. See `research/artifacts/thompson-v-amenable-actions-2026-09-16.md`, Sections 2–7. In
  a witness, almost every stabilizer `H` is proper. The items of
  `thompson-v-amenable-actions-are-free-off-fixed-points` then exclude the following.
  - **Confined stabilizers (item 3).** Dead for each confining set, and `φ_S(V/H) ≥ c_P` uniformly for
    `H` under a subgroup confined by `P`. The union over all `P` is not controlled, since the mean is
    only finitely additive.
  - **Stabilizers fixing a Borel probability on the Cantor set (item 4).** Dead. This covers amenable
    subgroups, point stabilizers, stabilizers of finite configurations of any size, `F`, and
    Bernoulli-preserving subgroups.
    - Configuration spaces carry no invariant mean. This contrasts with item 2(I) of
      `thompson-f-mean-free-actions-dense-configurations-or-unconfined`.
  - **Rigid covers (item 5).** Dead. This covers stabilizers of proper clopen sets and of finite clopen
    partitions, and all subgroups of these, with a uniform isoperimetric constant.
  - **Stabilizers containing some `V_U`.** A survivor has `O(H) = ⋃{U : V_U ≤ H}` open and not closed.
    - The closed `H`-invariant set `C \ O(H)` carries no `H`-invariant probability.
    - Item 7 forces its translates to be dense at every fixed scale. That is no contradiction for a
      finitely additive mean.
  - **Wq*-normality.** The imported Tucker-Drob Theorem 1 (arXiv:1407.7474v3) makes almost every
    stabilizer wq*-normal. No contradiction was derived from it.
  - **Thompson's T.** `T` is the natural test case, and it remains undecided.
    - It is not in `𝓜`, contains no `V_U`, and preserves no finite clopen partition.
    - It lies below no member of `𝓒`. If `T ≤ K` and `K` contains some `V_[w]`, then transitivity of `T`
      on proper dyadic arcs puts every `V_U` with `U` proper in `K`, and simplicity gives `K = V`
      (artifact §7).
    - So items 4 and 5 and the rigid-stabilizer bullet do not apply. Confinement is the only exclusion
      not decided for `T`.
    - Whether `T` is confined, and whether `φ_S(V/T) = 0`, is open here.
  - **Confined-subgroup classifications.** Le Boudec–Matte Bon, arXiv:2012.03997v2, §5, was read only
    for highly transitive actions of `V_d`. It was not used as a classification of confined subgroups.
  - **Where it dies.** The candidates are proper subgroups outside the downward closures of `𝓜`, `𝓒`
    and the confined subgroups. No candidate was produced, and no uniform isoperimetric bound over all
    proper `H` was proved.
- **2026-09-17, sw-127 (scale-shifter, lane `thompson-v-surjunctive`).** The test candidate `Ω = V/T` is
  dead. `T` is not co-amenable in `V`, so `φ_S(V/T) > 0`
  (`thompson-v-finitary-structure-stabilizers-are-not-co-amenable`).
  - **Chain check.** "`T` co-amenable ⇒ `V` sofic ⇒ surjunctive" is sound. It is item 1 of
    `thompson-v-amenable-actions-are-free-off-fixed-points` followed by Gromov–Weiss. It dies at its hypothesis.
  - **Where it dies.** `T = Stab_V(σ)`, where `σ` is the circle involution of the dyadic points
    `Q = {w0^∞, w1^∞}`. A coset `gT` has a finite breakpoint set `D(gT) = {z : gσg^(-1)z ≠ σz}`, and
    `|D(hgT) Δ hD(gT)| <= 2|D(hT)|`. An invariant mean on `V/T` gives mass zero to bounded breakpoint sets,
    by disjoint translates. Averaging uniform measures on breakpoint sets then yields an invariant mean on `Q`,
    which the halving map forbids.
  - **Class killed.** Every subgroup of a conjugate of `Stab(σ)`, for any structure `σ` over a mean-free
    `V`-set `Q` whose `V`-moves are finite perturbations with unbounded defect. This includes `F` and `T`.
    The same holds over `Q = V/K` for any non-co-amenable `K`, so the class iterates.
  - **What remains.** Candidates must avoid the downward closures of `𝓜`, `𝓒`, confined subgroups, and
    finitary-structure stabilizers. The claim itself is not refuted.
