---
rg: 2
id: commutative-algebra-affine-groups-have-polynomial-word-problem
kind: claim
title: Finitely generated affine groups of finitely generated modules over finitely generated commutative algebras over finite fields have polynomial-time word problem
distinct_from:
  complexity-bounded-host-classes-are-not-universal: that is the general principle turning a shared recursive word-problem bound into non-universality; this proves that one concrete class of hosts has such a bound.
  rational-homeomorphism-subgroups-have-exponential-wp: that bounds groups of rational Cantor homeomorphisms; this bounds affine groups of modules over finitely generated commutative algebras of positive characteristic, which need not be linear over a field.
  char-p-linear-groups-satisfy-permutational-boone-higman: that places positive-characteristic linear groups in B_A through the hosts R^N x| E_N(R) with R = F_p[s_1..s_k]; this bounds the word problem of every such host and of their module and non-reduced generalizations.
artifacts:
  - research/artifacts/solve-kms-self-similar-affine-2026-09-13.md
---

**ESTABLISHED** by `commutative-algebra-affine-groups-polynomial-word-problem-proof`.
Elementary; no novelty is claimed. Not independently reviewed.

## Statement

Let `q` be a prime power, `R` a finitely generated commutative `F_q`-algebra, `S`
a finitely generated `R`-module, and

    Aff_R(S) = S x| Aut_R(S),   (s, w) · x = s + w(x).

1. **Polynomial word problem.** Let `Γ <= Aff_R(S)` be finitely generated, with a
   finite generating set `B`. There is a constant `C`, depending on `Γ` and `B`,
   such that the word problem of `Γ` over `B` is decidable in time `C*l^C + C` on
   words of length `l`.
2. **One bound for the whole class.** Put `g(n) = 2^n` and
   `F(g) = { L : L decidable in time C*g(C*n) + C*n + C for some C }`, as in
   `(UWB1)` of `uniform-wp-bound-excludes-bh-universal-targets`. Every finitely
   generated subgroup of every `Aff_R(S)` above has word problem in `F(g)`.

## What it covers

- `GL_n(R)` (take `S = R^n` and zero translations) and `R^n x| GL_n(R)`, for every
  finitely generated commutative `F_q`-algebra `R`, including rings with nilpotents.
  Their finitely generated subgroups need not be linear over any field.
- In particular the finitely presented self-similar hosts `R^N x| E_N(R)`,
  `R = F_p[s_1, ..., s_k]`, of `char-p-linear-pbh-via-polynomial-self-similar-hosts`.
- Affine actions on modules with torsion, such as `F_p[t^(±1), (t-1)^(-1)]` for
  Baumslag's group.

## Scope

- Only algebras over finite fields. Finitely generated commutative rings of mixed or
  zero characteristic are not treated here.
- Nothing is said about non-commutative algebras. There the word problem of `R` itself
  can be as hard as any recursive set.

## Trust surface

Two standard facts about Gröbner bases, not re-read at source (Cox--Little--O'Shea,
*Ideals, Varieties, and Algorithms*, Ch. 2): the division algorithm with its
leading-monomial bound, and the criterion that `f` lies in an ideal exactly when its
remainder on division by a Gröbner basis of that ideal is zero.
