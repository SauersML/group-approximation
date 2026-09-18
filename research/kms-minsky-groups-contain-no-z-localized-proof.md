---
rg: 2
id: kms-minsky-groups-contain-no-z-localized-proof
kind: route
title: Torsion-free subgroups of a finitely generated torsion-by-abelian group embed in its finitely generated abelian quotient
target: kms-minsky-groups-contain-no-z-localized
requires: []
---

Direct proof, with one import: Theorem 4.3(a) of Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506v5,
quoted in the target.

**The general lemma.** Let `G` be a finitely generated group with a normal subgroup `N` of finite
exponent `d` such that `G/N` is abelian. Let `S <= G` be torsion-free.
- `S ∩ N = 1`: every element of `N` has order dividing `d`, and `S` has no nontrivial torsion.
- So `S` embeds in `G/N`.
- `G/N` is a finitely generated abelian group, and its torsion-free subgroups are free abelian of finite
  rank.

**Application.** Theorem 4.3(a) puts `G(M)` in `𝒜_p^2 𝒜`.
- So there is a normal subgroup `N` which is an extension of an abelian group of exponent `p` by one of
  exponent `p`. Hence `N` has exponent dividing `p^2`, and `G(M)/N` is abelian.
- `G(M)` is finitely generated (§4.1). The lemma applies with `d = p^2`.
- Either reading of `𝒜_p^2`, as `𝒜_p 𝒜_p` or as abelian of exponent `p^2`, gives a normal subgroup
  of finite exponent with abelian quotient, which is all the lemma uses. The same follows from
  Lemmas 4.4 and 4.5 of the source: `T` is abelian of exponent `p`, and
  `G(M)/T ≅ <H_1 ∪ H_2>` is (exponent-`p` abelian) ⋊ (abelian).

**Consequences.**
- *`Z[1/q]`.* It is torsion-free and not finitely generated, since `1` has `q^j`-th roots for every `j`.
  So it is not free abelian of finite rank.
- *`Z_(l)`, `Z[1/P]` with `P` nonempty, `(Q,+)`.* Each contains some `Z[1/q]`.
- *`G_l`.* It contains `Z_(l) f_0`.

So none of these embeds in any `G(M)`. ∎
