---
rg: 2
id: fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank
kind: claim
title: In every free action of a finitely generated free group, the sandwich cost over any finitely generated subgroup H is the least rank of a subgroup between H and the group, so the relative sandwich Bernoulli bound holds for all free groups
distinct_from:
  fpbs-sandwich-cost-fox-rank-lower-bound: that proves C(E) >= rk(Fox matrix) and evaluates it only for compressed H; this evaluates the bound for every finitely generated H and matches it with an explicit group sandwich, so it computes p_H exactly for non-compressed H too.
  fpbs-free-group-sandwich-cost-is-two: that is the F_2 case, where every non-cyclic H has minimal overgroup rank 2; this is every finite rank, where non-compressed H of minimal overgroup rank strictly between 1 and rk H occur.
  fpbs-relative-sandwich-cost-bernoulli-lower-bound: that is RBL for every finitely generated group; this proves it for every finitely generated free group and every finite F, with the exact value.
---

**ESTABLISHED** through
[[fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank-proof]].

Let `Δ` be a free group of finite rank `q ≥ 1`, let `F ⊆ Δ` be finite, put
`H = ⟨F⟩`, and let `a` be any free p.m.p. action of `Δ`. Then

```text
p^Δ_F(a) = inf{ C(E) : E_{a|H} ⊆ E ⊆ E_a } = π̄(H ≤ Δ) = min{ rk L : H ≤ L ≤ Δ },
```

and the infimum is attained by `E = E_{a|L}` for any `L` of minimal rank.

**Consequences.**
- `p^Δ_F` is constant on free actions of every finitely generated free group.
  In particular `p^Δ_F(s_Δ) ≤ p^Δ_F(a)` for every free `a`: this is
  `fpbs-relative-sandwich-cost-bernoulli-lower-bound` for all finitely
  generated free `Δ`, not only `F_2`.
- Every sandwich is at least as expensive as the cheapest *group* sandwich.
  Measurable, non-group, twisted sandwiches never beat subgroups. This is a
  measured form of "a subgroup containing `H` has rank at least `π̄(H)`".
- A non-compressed case the earlier nodes do not reach: in
  `F_3 = ⟨x, y, z⟩` take `H = ⟨x, y x y^{-1}, y^2⟩`. It is the kernel of the
  `y`-parity map `⟨x, y⟩ → Z/2`, so it has index 2 in `⟨x, y⟩` and rank 3.
  It is non-abelian, so `π̄(H ≤ F_3) = 2 < 3 = rk H`. Every sandwich over
  `H`, in every free action of `F_3`, costs at least 2, and `E_{a|⟨x,y⟩}`
  costs exactly 2.

**What it does not do (remark, not used).** It says nothing about non-free
`Δ`. The Fox cocycle needs a derivation `δ: Δ → (ZΔ)^{1×q}` with
`δ(f_k) = e_k`. Derivations are `Hom_{ZΔ}(I_Δ, −)`, so such a `δ` splits the
surjection `(ZΔ)^q → I_Δ`, `e_k ↦ f_k − 1`, and is inverse to it. Then `I_Δ`
is free on the `f_k − 1`, the relation module of `F → Δ` vanishes, and `Δ` is
free on `f`. So the method stops exactly at free groups, and RBL for non-free
`Δ` stays open.
