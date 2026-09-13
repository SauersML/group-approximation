---
rg: 2
id: braid-groups-on-four-or-more-strands-are-not-self-similar
kind: claim
title: For n >= 4 the braid group B_n has no faithful state-closed action on any regular rooted tree
distinct_from:
  baumslag-char-zero-metabelian-group-is-not-self-similar: that obstructs self-similarity of one metabelian group through ring symmetries of its derived subgroup; this obstructs self-similarity of the braid groups through the geometric rigidity of injections of finite-index subgroups of B_n modulo its center.
  braid-groups-on-at-most-three-strands-are-self-similar: that constructs self-similar actions for n <= 3, where B_3 / Z(B_3) = PSL_2(Z) has a dense commensurator; this shows the construction cannot exist once n >= 4.
---

**ESTABLISHED, through a cited rigidity theorem.** Review PASS by
z-verify-groups at 822b3ac5f2 (`research/artifacts/zp-review-groups-2026-09-13-part2.md`
§10, landed d228d90964). Its wording fix, restating step 2 of the joint-core
argument with subgroups, is applied in the route. A novelty check is pending.
The finite-index-subgroup scope remark below was added after the review.

For every `n >= 4` and every `d >= 2`, every homomorphism `B_n -> Aut(T_d)`
with state-closed image has nontrivial kernel. So `B_n` is not self-similar in
Zaremsky's sense (arXiv:2405.09722), transitively or not.

## Mechanism

A faithful state-closed action gives virtual endomorphisms `f_i : H_i -> B_n`,
one per first-level orbit, with trivial joint core (Dantas–Santos–Sidki,
arXiv:2004.08941). Put `L_i = f_i^-1(Z(B_n))`. Each `f_i` is of one of two kinds:

- **(a)** `L_i` is not central. Then `f_i` kills a nontrivial normal subgroup of
  `B_n` with noncentral image in `Q = B_n / Z(B_n)`.
- **(b)** `L_i` is central. Then `f_i` induces an injective homomorphism from a
  finite-index subgroup of `Q` into `Q`. By
  `finite-index-injections-into-braid-quotients-are-geometric`, that
  homomorphism is conjugation by an extended mapping class of `S_(0,n+1)`.

In both cases the maps preserve a suitable nontrivial normal subgroup `K`: one
contained in the commutator subgroup, killed by every kind-(a) map, and whose
image in `Q` is normal in `Mod^±(S_(0,n+1))`. Such a `K` exists because nontrivial
normal subgroups of finite-index subgroups of `Mod^±(S_(0,n+1))` never commute,
and because `[B_n, B_n] ∩ Z(B_n) = 1`. So `K` lies in the joint core, and the
action is not faithful. Derivation:
`braid-non-self-similarity-via-geometric-injections`.

## Scope: finite-index subgroups

The same proof applies to every finite-index subgroup `G'` of `B_n` with `n >= 4`,
for example the pure braid group `P_n`. The substitutions:
- `Z(G') = G' ∩ Z(B_n)`, because the centralizer of `pi(G')`, a finite-index
  subgroup of `Mod^±(S_(0,n+1))`, is trivial (Lemma A, step 1);
- the exponent sum is still nonzero on `Z(G')`, so `[G',G'] ∩ Z(G') = 1`;
- `pi(G')` has finite index in `Mod^±(S_(0,n+1))`, so Lemma A and the rigidity
  claim apply unchanged, with `core_(G')` in place of `core_G`.

So no finite-index subgroup of `B_n` with `n >= 4` is self-similar (unreviewed).
This does not exclude self-similar overgroups: containing `B_n` is a different
question, the Part 2 territory of Problem 3.9.

## Contrast with n = 3

`B_3 / Z(B_3) = PSL_2(Z)` is virtually free, and conjugation by `diag(2,1)` is an
injective virtual endomorphism that is not a conjugation inside `PSL_2(Z)`. That
is exactly what the `B_3` construction uses
(`braid-groups-three-strands-self-similar-proof`), and it is exactly what rigidity
forbids for `n >= 4`. The pattern matches Kapovich, arXiv:0809.0323: lattices
admit faithful self-similar actions iff they are virtually arithmetic, i.e. iff
their commensurator is large.
