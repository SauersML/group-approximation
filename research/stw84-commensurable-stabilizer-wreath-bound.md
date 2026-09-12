---
rg: 2
id: stw84-commensurable-stabilizer-wreath-bound
kind: claim
title: A nonsplit common commensurability core gives finite nuclear dimension for permutation wreath products
distinct_from:
  stw84-common-stabilizer-wreath-bound: that requires a literal decomposition A=H direct_sum Q; here H need not be a direct summand and the infinite stabilizers may vary through finite extensions of H.
  stw84-almost-free-permutation-wreath-bound: that requires finite point stabilizers; here every point stabilizer can have the same positive rational rank.
  stw84-kernel-finite-locally-finite-by-abelian-computation: the regular residual orbit in the displayed example makes a two-generated subgroup meet the lamp kernel infinitely.
artifacts:
  - research/artifacts/stw84-commensurable-stabilizer-wreath-2026-08-30.md
---

Let `L` be a countable locally finite group, let `A` be a countable abelian
group of finite rational rank `r`, and let `A` act on a countable set `S`.
Suppose there is a subgroup `H<=A` such that

1. `H` fixes every point of `S`; and
2. `A_s/H` is finite for every `s in S`.

Set

`h=rank_Q(H)` and `q=rank_Q(A/H)=r-h`.

No splitting of `0 -> H -> A -> A/H -> 0` is assumed.  Define

`t(q)=sup dim_nuc C*(M,sigma)`,

where the supremum runs over all finitely generated abelian groups `M` of
rational rank at most `q` and all scalar two-cocycles `sigma` on `M`.
Eckhardt--Wu's twisted virtually-polycyclic theorem makes `t(q)` finite; put
`b(q)=max{1,t(q)}`.  If `q>=1`, then

`r <= dim_nuc C*((direct_sum_S L) rtimes A)`

`   <= 9^r (h+1)(b(q)+1)-1 < infinity`.                 `(CMW1)`

If `q=0`, the exact value is

`dim_nuc C*((direct_sum_S L) rtimes A)=h=r`.             `(CMW2)`

Thus the split common-core theorem extends to orbit-dependent infinite
stabilizers which are finite extensions of one possibly nonsplit core.  In
particular, finitely many pairwise commensurable stabilizer types are covered
after replacing the types by their intersection.

For a genuinely nonsplit example, let

`A=Z[1/2] direct_sum Z`, `H=Z direct_sum 0`,

and write `Q=A/H=(Z[1/2]/Z) direct_sum Z`.  If `c_n=2^(-n)+Z`, let `S` be
the disjoint union of the regular `Q`-set and the coset sets
`Q/<c_n>`, pulled back to an `A`-action.  Its stabilizers are `H` and the
varying groups `pi^(-1)(<c_n>)`; all have rank one and finite quotient over
`H`.  The extension does not split because `A` is torsion-free while `A/H`
has nonzero torsion.  With any nontrivial finite lamp, `(CMW1)` gives finite
nuclear dimension although the earlier split theorem does not apply.
