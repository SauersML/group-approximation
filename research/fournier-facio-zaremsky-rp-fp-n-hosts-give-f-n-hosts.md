---
rg: 2
id: fournier-facio-zaremsky-rp-fp-n-hosts-give-f-n-hosts
kind: claim
title: "If every finitely generated recursively presented group has a recursively presented FP_n host, every finitely presented group has an F_n host"
distinct_from:
  higman-rope-trick-group-is-never-fp3: that is Theorem B of the same paper, an obstruction to one construction; this is Theorem A, a reduction of homotopical hosts to homological ones
---

Francesco Fournier-Facio and Matthew C. B. Zaremsky, *Finiteness properties
and Higman's rope trick*, arXiv:2607.21727v1 (submitted 23 July 2026),
Theorem A, verbatim: "Let n∈ℕ∪{∞}. If every finitely generated recursively
presented group embeds into a recursively presented group of type FP_n, then
every finitely presented group embeds into a group of type F_n."

The proof (their Section 2, "From homological to homotopical") has two steps.

1. Lemma 2.1: "If a finitely presented group G is of type FP_n, then it is of
   type F_n." One attaches finitely many orbits of cells, generating
   `H_{n-1} = π_{n-1}` of the `(n-1)`-skeleton, which is finitely generated
   over `ZG` by `FP_n`.
2. Take `G` a universal finitely presented group, an embedding `ι: G -> H`
   with `H` recursively presented of type `FP_n`, and an embedding
   `j: H -> G` (Higman). The ascending HNN extension `E` of `G` along `jι` is
   finitely presented. It is also an ascending HNN extension of `j(H) ≅ H`,
   because `t j(H) t^{-1} ⊂ tGt^{-1} = jι(G) ⊂ j(H)`, `E = <j(H), t>` and
   `t^k ∉ j(H)` for `k ≠ 0`. So `E` is of type `FP_n` (Bieri 1981), hence of
   type `F_n` by Lemma 2.1, and `G <= E`.

The converse implication is immediate: an `F_n` host is finitely presented,
hence recursively presented, and of type `FP_n`, and every finitely generated
recursively presented group embeds in a finitely presented group (Higman).
So for each `n` the two statements are equivalent.

Consumers: `f-infinity-hosts-via-rp-fp-infinity-hosts` and
`type-fn-plus-1-hosts-via-rp-fp-n-hosts`, into the affirmative answers of
Zaremsky Problem 1.1.
