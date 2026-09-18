---
rg: 2
id: lk-b4-never-proximal-on-finite-index-subgroups
kind: claim
title: At every specialization and every absolute value, Lawrence–Krammer for B_4 is not Θ-proximal on any finite-index subgroup, so no proximal Schottky certificate exists
distinct_from:
  lawrence-krammer-has-a-faithful-algebraic-unit-specialization: that asks whether some unit specialization is faithful; this proves that one method of certifying faithfulness, proximal ping-pong on flag varieties, fails at every specialization
---

**Setting.** Let `ρ_(q,t)` be the Lawrence–Krammer representation of `B_4` on `Z[q^±1, t^±1]^6`, in Krammer's
form (matrices in `experiments/braid-tropical-pingpong-2026-09-17/lk.py`). Put `a = s1 s3^-1`,
`b = s2 a s2^-1` and `c = [a, b] = a b a^-1 b^-1`. Then `a` and `b` generate the free group
`F_2 = ker(B_4 -> B_3)`.

**Claim.** Let `K` be a field with an absolute value `|·|` (archimedean or not), let `q_0, t_0 ∈ K^*`, and put
`ρ = ρ_(q_0, t_0)`. Let `H <= B_4` contain nontrivial powers of a conjugate of `a` and of a conjugate of `c`.
This holds for every finite-index subgroup of `F_2` or of `B_4`. Then for every `k ∈ {1, ..., 5}` there is
`h ∈ H` such that the eigenvalues of `ρ(h)`, ordered by decreasing absolute value, satisfy
`|λ_k| = |λ_(k+1)|`. The eigenvalues involved all lie in `K`.

**Consequences.**

- For no nonempty `Θ ⊆ {1, ..., 5}` are all nontrivial elements of `ρ(H)` Θ-proximal. So no P_Θ-Schottky
  certificate (ping-pong with proximal generators on `Gr_k(K^6)` or on a partial flag variety) exists for
  such `H`, over any valued field and at any specialization.
- Over a local field, `ρ|_H` is not P_Θ-Anosov for any `Θ`. This uses the standard fact that Anosov
  representations send infinite-order elements to Θ-proximal ones.
- The proximal-Schottky route to a faithful unit specialization on `F_2` is dead. That route is the
  `experiments/braid-tropical-pingpong-2026-09-17/README.md` plan for
  `lawrence-krammer-has-a-faithful-algebraic-unit-specialization`, and it would suffice because
  `ker ρ ∩ F_2 = 1` forces `ker ρ` to be central.
- Any ping-pong proof of faithfulness for `LK_4` on a finite-index subgroup of `F_2` must use non-proximal
  dynamics, such as Jordan blocks or reducible pieces.

**Scope.** This is about `LK_4` only. It says nothing about other representations of `B_4`, or about
faithfulness mechanisms other than proximal ping-pong.

Proof: `lk-b4-never-proximal-on-finite-index-subgroups-proof`.
