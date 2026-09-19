---
rg: 2
id: shell-germ-singular-ideal-is-the-boundary-annihilator
kind: claim
title: The local singular ideal of a shell germ algebra is the annihilator of the permutation module on the Schreier boundary of the germ group's near action
distinct_from:
  shell-germ-singular-ideal-is-generated-at-the-singular-point: that defines J_p as the annihilator of the shell module K^N/K^(N) and reduces finite generation of J to it; this rewrites that annihilator as an intersection of induced-module annihilators indexed by the limit stabilizers at infinity.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Setting

`Q` is the germ group at `p` of a shell envelope, near-acting on `N`, and
`J_p = Ann_(K[Q])(K^N / K^(N))`, as in
`shell-germ-singular-ideal-is-generated-at-the-singular-point`. Each `q ∈ Q` has a representative
`σ_q`, defined and injective on `[N_q, ∞)`, and two representatives of `q` agree on large `n`.

**Schreier boundary.** For large `n`, put `Stab(n) = {q : σ_q(n) = n}`. For each fixed `q`,
membership is well defined once `n >= N_q`. A *limit stabilizer* is a pointwise limit
`H = lim Stab(n_i)` with `n_i -> ∞`. Such limits exist along subsequences, since `Q` is
countable. Each one is a subgroup, because `σ_(qq') = σ_q σ_(q')` on large `n`. The set `𝓛` of
limit stabilizers is closed in `Sub(Q)`. It is invariant under conjugation, because moving the
points `n_i` to `σ_q(n_i)` gives the limit `qHq^(-1)`.

## Statement

    J_p = ∩_(H ∈ 𝓛) K[Q] ω(H) = Ann_(K[Q]) ( ⊕_(H ∈ 𝓛) K[Q/H] ).

In words, `K[Q]/J_p` (the germ algebra at `p` of `A/J`) is the image of `K[Q]` acting on the
permutation modules `Ind_H^Q K` of the Schreier boundary.

## Proof

Let `x = Σ_(q ∈ T) c_q q`, with `T` finite.
- **What `x e_n = 0` depends on.** For large `n`, `σ_q(n) = σ_(q')(n)` iff `q^(-1) q' ∈ Stab(n)`.
  So `x e_n = 0` iff the coefficients cancel on each class of that relation, i.e. iff
  `x e_H = 0` in `K[Q/H]` for every `H` with `H ∩ T^(-1)T = Stab(n) ∩ T^(-1)T`.
- **`J_p ⊆` the intersection.** If `x ∈ J_p`, then `x e_n = 0` for large `n`. Every `H ∈ 𝓛`
  agrees on the finite set `T^(-1)T` with `Stab(n)` for some large `n`. So `x e_H = 0`.
- **The intersection `⊆ J_p`.** If `x ∉ J_p`, the sparse-sum test gives infinitely many `n`
  with `x e_n ≠ 0`. A limit `H` of their stabilizers agrees with `Stab(n_i)` on `T^(-1)T` for
  large `i`, so `x e_H ≠ 0`.
- **Identifying the pieces.** The kernel of `x |-> x e_H` is the left ideal `K[Q] ω(H)`. Since
  `𝓛` is conjugation-invariant, the intersection over `𝓛` equals the annihilator of the
  direct sum. `∎`

## Instances

- **Zigzag shell of `Z`** (`zigzag-shell-singular-ideal-is-finitely-generated`). `𝓛` is four
  conjugate subgroups, one per residue class mod 4. For class `0` it is `H_0 = <y, xt>`, which
  matches the prime `(y - 1, xt - 1)` there.
- **Generic shells** (`generic-shells-have-infinitely-generated-singular-ideals`). `𝓛` is one
  conjugacy class, `{F_o, F_e}` up to conjugacy, and `J_p = ω(F_e) ω(F_o) K[Q]` is not finitely
  generated.

## Lesson for general BH

Finite generation of the singular ideal is a property of the Schreier boundary `𝓛` of the
germ group, read linearly: it asks whether `∩_(H ∈ 𝓛) K[Q] ω(H)` is finitely generated as a
two-sided ideal. So the question for the `A/J` algebra route is a question about limit
Schreier graphs at infinity, which is where the group gates also live.
