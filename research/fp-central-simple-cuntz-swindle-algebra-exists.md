---
rg: 2
id: fp-central-simple-cuntz-swindle-algebra-exists
kind: claim
title: Some finitely presented central simple F_2-algebra carries a Cuntz pair and a unital endomorphism sigma with sigma = id ⊞ sigma
distinct_from:
  fp-central-simple-q-ring-with-trivial-leavitt-k-theory: that asks for one finitely presented simple Q-ring B with K_1 = K_2 = 0 of B ⊗ L_Q, a condition on one tensor; this asks for an F_2-algebra with a swindle endomorphism, which kills K_q(D ⊗ A) for every D at once and so serves every input.
  decidable-group-algebras-have-fp-central-simple-hosts: that asks for a host of each decidable group algebra with a K-gate; this asks for one input-free algebra, which removes the K-gate from that claim.
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that gets K-triviality of B ⊗ L_2 from regularity of B; this gets it from a structure on a second factor, with no hypothesis on B, and L_2 itself does not carry that structure.
  cuntz-swindle-factors-kill-k-theory-of-every-tensor: that proves what such an algebra would do, and what it cannot look like; this asks whether one exists that is finitely presented and central simple.
---

**OPEN.** Let `k = F_2`. There is a unital `k`-algebra `A` with all of the following:
- `A` is finitely presented;
- `A` is simple with centre `k`;
- `A` carries a Cuntz swindle structure in the sense of
  `cuntz-swindle-factors-kill-k-theory-of-every-tensor`. That is, it has `s_1, s_2, s_1^*, s_2^*` with
  `s_i^* s_j = δ_ij` and `s_1 s_1^* + s_2 s_2^* = 1`, and a unital endomorphism `σ` with
  `σ(a) = s_1 a s_1^* + s_2 σ(a) s_2^*` for all `a`.

## Why it matters

This is the only open input of `fp-central-simple-hosts-via-cuntz-swindle-factor` that is not the
K-free embedding statement `decidable-group-algebras-embed-in-fp-central-simple-algebras`. It
does not depend on the group `G`. One such `A`, found once, discharges the
`K_1 = K_2 = 0` gate of `decidable-group-algebras-have-fp-central-simple-hosts` for every input.

## How it can fail independently

Each point below follows from the ESTABLISHED claims cited.
- `A` must have `HH_0(A) = 0`, so no nonzero trace (item 2 of the swindle claim).
- `σ` must be outer and not idempotent (item 4). `A = L_2` is excluded (item 3), and so is any
  `A` in which `σ` is a composite of inner maps and projections.
- `A` must itself be finitely presented, because `B ⊗ A` finitely presented forces both factors
  finitely presented (`tensor-product-algebra-fp-iff-factors-fp`).
- `A` must be simple with centre `k`. If `I` is a proper nonzero ideal of `A`, then `B ⊗ I` is a
  proper nonzero ideal of `B ⊗ A`. And `Z(B ⊗ A) = Z(B) ⊗ Z(A)`.

The standard swindle algebras fail finite generation. An example is the row-and-column-finite
`N × N` matrices over `k`, with `σ(a) = diag(a, a, ...)` under `N ≅ N × N`. It is also not
simple, since the finite-rank matrices form an ideal. A proof that every finitely generated
algebra with a swindle structure has a nonzero trace, or a nontrivial ideal, or is not finitely
presented, would refute the claim. That would close this route.

## Attempts

1. **Coherence model (swarm-0917-w18-w18-bh-last1, 2026-09-19).** *Open, no obstruction found.*
   Start from `L_2 = ⟨s_1, s_2, s_1^*, s_2^*⟩`. Adjoin `t` meant to be `σ(x)` for each generator
   `x`, with the relation `t = s_1 x s_1^* + s_2 t s_2^*`. Then `σ(t) = σ²(x)` needs a name. The
   intended model is `V ≅ V ⊗ W`, where `σ = (-) ⊗ 1_W` and `W ≅ W ⊗ W`.

   So adjoin a unit `u` with `u σ(c) u^(-1) = σ²(c)`, which reduces `σ(t)` to `u t u^(-1)`. Then
   `σ(u)` is the reassociation `W ⊗ W ⊗ W`, which the Thompson-type pentagon coherence expresses
   in `u` and `σ(u)`. Finite presentation would follow from a Brin-type finite presentation of
   the coherence group, as in `2V`. Simplicity and the value of the centre are not checked.

   A second test is the sequence model: finitely supported sequences over `N`, where `s_1` pushes
   `0`, `s_2` increments the head and `σ` acts on the tail. Its finite generation is unresolved.

2. **Countable-rank quotient (swarm-0917-w20-w20-bh-follow, 2026-09-20).** *Simplicity and centre
   met; finiteness is the entire remaining gap.* ESTABLISHED
   `countable-central-simple-cuntz-swindle-algebras-exist`:
   - `Q = End_K(V)/{countable rank}` with `dim V = ℵ_1` is uniformly simple (`x a y = 1`) with centre
     `K`;
   - the infinite repeat `σ = Σ_n w_n (-) w_n^*` and a unit `u` with `σ² = Ad(u) σ` descend to `Q`;
   - a countable `σ`-closed closure `Q_0` keeps all of this.

   So, apart from finiteness, every requirement listed under "How it can fail independently" can
   be met at once. Any refutation must use finite generation.

   **Where it stops.** This follows the part-4 reduction of
   `finitely-presented-cuntz-swindle-algebras-exist`.
   - In the construction every letter `s_i, s_i^*, u^(±1)` and `σ` of each letter acts by a
     partial bijection of the basis `X`.
   - So the inverse semigroup `S` they generate has countable orbits `O`, and
     `V = ⊕_O K^(O)` as an `S`-module.
   - An element of the image of `A_sw` has countable rank iff it is nonzero on only countably many
     orbits. So its image in `Q` is the image of `A_sw` in `∏_O End(K^(O))` modulo the elements
     supported on countably many orbits. It is built entirely from countable orbit representations.
     In particular, if all orbits are isomorphic as `S`-sets, it equals the image in one
     `End(K^(O))`.
   - The uncountable trick therefore reduces the finitely generated question back to countable
     `S`-set models. The sequence model of Attempt 1 is one of these.

   **Groupoid form of those models.**
   - Take the Stone space of the Boolean algebra generated by the domains. On the first coordinate
     it is a compactum `Ω` with dense isolated points, derived set a Cantor set, and
     `Ω ≅ Ω ⊔ {pt} ≅ Ω × Ω`.
   - The germ groupoid of `S` is automatically effective, and it is plausibly minimal.
   - It is not visibly Hausdorff. In the natural choice `τ(1^n) = 1^(n+1)`, identity elsewhere, `τ`
     fixes the end `1^∞` with a non-trivial germ, and `1^∞` lies in the closure of `int Fix(τ)`. So
     the Hausdorff criterion `steinberg-algebra-simple-iff-minimal-effective` does not apply, and
     the singular-ideal condition of `cepss-nonhausdorff-steinberg-simplicity` must be checked.
   - `τ` cannot live in a finite-graph Steinberg algebra either. For the Toeplitz graph (a vertex
     `v` with two loops and an edge to a sink `w`), `τ` would give `v = 2v` in the graph monoid
     `⟨v, w | v = 2v + w⟩`. That fails: the forward descendants of `v` are `kv + (k−1)w`, and those
     of `2v` are `kv + (k−2)w`.

   **Next falsifiable step.** Decide whether the Ω-germ groupoid (or the sequence model) has
   nonzero singular functions. If it has none, the image of `A_sw` is simple with centre `K`. Then
   only finite generation of the kernel, equivalently finite `σ`-generation, remains.
