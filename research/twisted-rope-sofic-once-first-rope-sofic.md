---
rg: 2
id: twisted-rope-sofic-once-first-rope-sofic
kind: claim
title: On INF the compiler's twisted rope R_e is sofic whenever its first rope Gamma_e is sofic
distinct_from:
  compiler-rope-edge-is-not-co-amenable: that reduces the first rope Gamma_e to one two-sided action; this is the second, twisted rope, assuming Gamma_e sofic.
  regular-mf-tensor-sync-proves-twisted-rope-mf: that proves the operator-MF version through the universal HNN algebra of Ueda and Shulman; this asks for soficity, where no universal-algebra injectivity step exists.
  centralizing-hnn-perturbed-edge-separation: that is Britton separation for the first rope's edge L_e in K_e; this concerns the edge S_e = F *_(N_e) F^v inside the first rope itself.
  twisted-rope-is-a-central-rope-over-an-rf-envelope: that proves the embedding into a central rope over a residually finite envelope; this is the soficity conclusion, still open.
---

OPEN. Take the compiler of [[mf-safe-finite-presentation-compiler]] and
`e in INF`. If `Gamma_e = < K_e, v | [v, L_e] = 1 >` is sofic, then

```text
R_e = < Gamma_e x Q_e, u | u(s,1)u^-1 = (s, tau_e(s)), s in S_e >,   S_e = F *_(N_e) F^v,
```

is sofic.

**Why it is needed.** `R_e` is the compiler's positive-branch output
([[finite-presentation-rice-criterion-via-the-fixed-positive-rope]]). The
first rope makes `Gamma_e` sofic, and this claim carries soficity across the
final edge. It is a premise of [[centralizing-hnn-sofic-strategy-route]].
Soficity of `Gamma_e` is necessary, because `Gamma_e <= R_e`.

**What is known.** By [[twisted-rope-is-a-central-rope-over-an-rf-envelope]]
the twist is inner in `D_e = Gamma_e x R-hat`, where `R-hat` is a fixed
residually finite group. So `R_e` embeds in the free generalized wreath
product over `D_e action D_e/C_e`, and the claim follows from
[[twisted-rope-envelope-coset-action-is-sofic]]. That in turn follows from
the first rope's action on its edge cosets,
[[first-rope-edge-coset-action-is-sofic]], by
[[envelope-coset-action-sofic-once-edge-coset-action-sofic]]. So the twist
adds nothing: under the same hypotheses GKP Theorem 3.7 makes the untwisted
rope `< Gamma_e, z | [z, S_e] = 1 >` sofic.

`R_e` has no infinite property (T) subgroup, so the Kun--Thom mechanism is
absent here too.

- A (T) subgroup fixes a vertex of the Bass--Serre tree, so it lies in a
  conjugate of `Gamma_e x H`.
- Its projections are (T) subgroups of `Gamma_e` and of `H`.
- `H <= F_2 x F_2`, so its projection to `H` is finite.
- `Gamma_e` acts on its own tree with vertex groups `K_e` and `L_e x Z`, both
  a-T-menable. So its projection to `Gamma_e` fixes a vertex there and is
  finite too.

## Attempts

- **The free-edge argument, verbatim (dies at step one).**
  [[centralizing-hnn-sofic-via-regular-edge-centralizer]] chooses the stable
  letter inside the centralizer (CE1) of one edge action. A twisted letter must
  conjugate two different restrictions of the base model to `S_e`, so (CE1)
  does not apply. One first needs those restrictions to be isomorphic
  `S_e`-sets. The sentence in the strategy route skips this.
- **Tensor-synchronized permutation models (partial).** Take any sofic model
  of `Gamma_e`, tensored with left-regular models of
  `image(r_n o Lambda, beta_n)`. This gives exact conjugacy of the two edge
  restrictions, with the edge acting freely wherever the `Gamma_e` model does.
  What is not proved is Britton separation of the stable letter. The finite
  factor kills `K_e^0` (assembly Section 3.4). The product-form conjugator
  `1 x W_n` provably kills `[u,(k,1)]`
  ([[final-rope-canonical-tensor-conjugator-is-not-faithful]]), so the letter
  must mix the two factors. In `Omega_e` the mixing is carried by the central
  letter `z`, which GKP Theorem 3.7 builds from coset-action models.
- **Inner envelope (works as a reduction; landed).**
  [[twisted-rope-is-a-central-rope-over-an-rf-envelope]] reduces the claim to
  soficity of one coset action of `Gamma_e x R-hat`.
