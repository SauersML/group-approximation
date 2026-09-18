---
rg: 2
id: mod-s2-opnorm-torelli-gap-via-finite-index-multipliers
kind: route
title: Reduce near-cube-root representations to Torelli-abelian ones, then read those as shifted Maslov multipliers on finite-index subgroups
target: mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap
requires:
  - mod-s2-near-scalar-reps-reduce-to-torelli-abelian
  - mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers
  - sp4-shifted-maslov-multipliers-stay-far-on-finite-index
---

**Route (open because two inputs are open).** Suppose the target fails. Since `Z_hon` is a subgroup closed
under negation, `1/3 in Z_hon`.

1. By `mod-s2-near-scalar-reps-reduce-to-torelli-abelian`, `1/3 in Z_ab`. OPEN; its finite-image case is
   established in `mod-s2-finite-image-near-scalar-reps-are-torelli-abelian`.
2. By `mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers` ((TA1) implies (TA2) at `alpha = 1/3`), for
   every `eta` there are a finite-index `Gamma'` and a `Gamma'`-invariant `h` with `|h| <= eta` such that
   `Phi_(Gamma')(h) - (1/(3r))[b]` is fd-realizable. ESTABLISHED.
3. This contradicts `sp4-shifted-maslov-multipliers-stay-far-on-finite-index` once `eta < eta_0`. OPEN.

**Division of labour.** Step 1 is a statement about honest representations with infinite image. Step 3 is pure
arithmetic of `Sp_4(Z)`: second cohomology of finite-index subgroups and finite-dimensional projective
realizability. Given step 1, step 3 is also necessary for the target, since (TA2) implies (TA1). So under step 1 the
target is equivalent to (D).
