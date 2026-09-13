---
rg: 2
id: kun-thom-action-soe-class-is-rigid
kind: claim
title: Every free action stably orbit equivalent to the diffuse Kun-Thom action is virtually conjugate to it, so none is mixing
invalidates: [mixing-nonsofic-action-via-soe-from-kun-thom-action]
distinct_from:
  kun-thom-free-nonsofic-action: that establishes nonsoficity of the Kun-Thom free action; this shows its stable orbit equivalence class contains nothing but finite-index copies of the same action
  sofic-free-actions-are-soe-invariant: that moves soficity along stable orbit equivalence; this shows that for the Kun-Thom seed the move produces no new group and no new dynamics
  popa-oe-superrigidity: that imports Popa's superrigidity theorems for all free s-malleable weakly mixing actions of w-rigid groups; this applies them to the one nonsofic action where they decide the fate of orbit-equivalence transfer
---

**ESTABLISHED (unreviewed).** Let `Γ <= G` with `Γ` and `G` Kazhdan, `Γ` infranormal and not
normal, and `G` with no nontrivial finite normal subgroup. Let `σ` be the diagonal action of
`G` on

```text
X = ([0,1], Leb)^(G/Γ) × ([0,1], Leb)^G,
```

the generalized Bernoulli action over the `G`-set `K = G/Γ ⊔ G`. Then:

1. `σ` is free, weakly mixing, s-malleable, and not sofic.
2. **SOE rigidity.** If a free ergodic p.m.p. action `θ` of a countable group `Λ` satisfies
   `ℛ_σ ≅ ℛ_θ^t` for some `t > 0`, then `1/t = n ∈ ℕ`, `Λ` has a subgroup `Λ_0 ≅ G` of index
   `n`, and `θ|Λ_0` on a `Λ_0`-invariant set of measure `1/n` is conjugate to `σ`. So `θ` is
   not mixing.
3. **Embedding rigidity.** If `ℛ_σ` is identified with a subrelation of `ℛ_θ^t` and every
   `σ(G)`-invariant finite subequivalence relation of `ℛ_θ^t` lies in `ℛ_σ`, then `t <= 1`,
   `σ` is conjugate to `θ|Λ_0` on a `Λ_0`-invariant set of measure `t` for some `Λ_0 ≅ G`, and
   `θ` is not mixing.

So stable orbit equivalence transfers the Kun--Thom nonsoficity only to finite-index
overgroups of copies of `G`, never to a mixing action. A mixing free action whose orbit
relation contains a copy of `ℛ_σ` must carry a `σ(G)`-invariant finite subequivalence
relation outside that copy.

Proof in `kun-thom-action-soe-class-is-rigid-proof`.

## Attempts

* **Containment without extra finite subrelations** is killed by clause 3. The surviving
  design must glue a `G`-invariant finite subequivalence relation onto `ℛ_σ`. Cocycle
  superrigidity for finite targets (`popa-bernoulli-cocycle-superrigidity`) untwists the
  index cocycle of the resulting finite-index extension, which is the next constraint to
  compute.
