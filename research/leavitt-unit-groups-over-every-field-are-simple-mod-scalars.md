---
rg: 2
id: leavitt-unit-groups-over-every-field-are-simple-mod-scalars
kind: claim
title: Over every field k the unit group of L_k(1,2) is perfect and simple modulo the scalars k^x
distinct_from:
  binary-leavitt-unit-group-is-simple: that is the field F_2, where the scalars are trivial and the unit group itself is simple; this is every field, modulo the central scalars.
  odd-leavitt-unit-groups-mod-scalars-are-fp-simple: that is the prime fields F_p, where the quotient is also finitely presented; this is simplicity alone, over every field, including Q and other infinite fields where the group is not finitely generated.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that is tensor hosts B ⊗ L_(F_p)(1,2) with B central simple over F_p, and its simplicity part assumes vanishing K_1 and K_2; this is the untensored algebra over an arbitrary field, where GL = EL is already a theorem and no K-theory is used.
  char-zero-leavitt-unit-groups-have-congruence-kernels: that shows the unit group over a finitely generated characteristic-zero domain is not simple; this is the unit group over a field, where the only obstruction is the centre.
  leavitt-units-embed-in-their-scalar-quotient: that embeds the unit group in its scalar quotient; this proves the scalar quotient simple.
---

**ESTABLISHED** by `leavitt-unit-groups-over-every-field-simple-mod-scalars-proof`
(paper assembly of Lean theorems proved for every field; not independently reviewed;
no novelty claimed).

Let `k` be a field, `R = L_k(1,2)`, `U = R^x`, and identify `k^x` with the central
scalar units. Then:
1. `U` is perfect.
2. Every normal subgroup of `U` is contained in `k^x` or equals `U`.
3. `U / k^x` is an infinite, nonabelian simple group.
4. For every `n >= 3`, `EL_n(R)` modulo its scalar centre `{λ I : λ ∈ k^x}` is simple.

## Consequence for GL_n(Q)

Take `k = Q` and put `Λ = L_Q(1,2)^x / Q^x`. For `n >= 1` let `a_i = 1^(i-1) 0`
(`1 <= i <= n`). Then `{a_1, ..., a_n, 1^n}` is a complete prefix code, and
```text
g  |->  Σ_(i,j<=n) g_ij s_(a_i) t_(a_j) + s_(1^n) t_(1^n)
```
is an injective homomorphism `GL_n(Q) -> U` (distinct code words are incomparable,
so `t_c s_c' = δ_(c,c')`, and the code is complete, so the idempotents sum to `1`).
- **Compatibility.** Splitting `1^n` into `1^n 0 = a_(n+1)` and `1^(n+1)` shows that
  the maps for `n` and `n+1` agree on `GL_n(Q) <= GL_(n+1)(Q)`.
- **No scalars.** The image of `g` times `s_(1^n)` is `s_(1^n)`. So an image equal to
  `λ` forces `λ = 1` and `g = 1`.

So `Λ` is a countable simple group that contains `GL_∞(Q) = ⋃_n GL_n(Q)`, and in
particular every `GL_n(Q)`. It also contains Thompson's `V` and `SL_3(Z)`.

`Λ` is not finitely generated (`infinite-field-leavitt-units-are-not-finitely-generated`).
So it is a natural *countable* simple overgroup of every `GL_n(Q)`, not a finitely
presented one. Embedding `Λ` itself in a finitely presented simple group is the open
statement `rational-leavitt-simple-group-embeds-in-fp-simple-group`, which would give
`gl-n-q-embeds-in-fp-simple-group` for all `n` at once.
