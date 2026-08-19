---
rg: 2
id: atlas-thirty-centralizer-products-classicalize
kind: claim
title: Near-membership in all thirty centralizer products forces approach to the finite classical alignment branches
distinct_from:
  atlas-a4-componentwise-commutant-collapse: that asks the frame to approach the COMMUTANT of two named packet-component subgroups; this asks it to approach the finite list of classical A8-automorphism alignment branches, which is a different target set -- a commutant is a group, the branch list is thirty points.
  atlas-a4-rank-three-core-commutant-collapse: same distinction, with the fourteen-word core and one commutant in place of thirty centralizer products.
  a4-near-context-centralizer-product-rounding: that is the ESTABLISHED per-context rounding -- one A4 relation, one centralizer product, dimension-uniform; this is the JOINT statement over all thirty at once, and the joint statement is not the conjunction of the individual ones because each product is a set, not a subgroup, and thirty near-memberships need not intersect near a common point.
artifacts:
  - research/artifacts/gpu-hyperlinear-attack-2026-08-19.md
---

OPEN.  This is the remaining mathematical breakthrough on the centralizer-
product route, and it is the only step of that route that is not proved.

Fix the canonical regular-`A_8` criterion, `rho_k = Reg(A_8) (x) I_k`, and let
`U_k in U(20160k)` be a relative chart frame.  `atlas-a4-packet-centralizer-
product-compiler` turns the thirty shortest `A_4` atlas relations into thirty
shifted centralizer-product constraints, so a hyperlinear sequence satisfies

```text
max_(1<=j<=30) dist_2(U_k, D_(j,k)) -> 0,
   D_(j,k) = C(rho_k(a_j)) C(rho_k(b_j))   (or the reversed product).
```

Ask: does that force

```text
dist_2(U_k, B_k) -> 0,
```

where `B_k` is the image in `U(20160k)` of the finite set of classical
`A_8`-automorphism alignments of the packet -- **uniformly in the
amplification `k`**?

**Why this is the whole difficulty.**  Each `D_(j,k)` is a product of two
centralizers, hence a set and not a group, and near-membership in thirty such
sets is a joint condition with no obvious common refinement.  Amplification is
where it bites: at fixed `k` a compactness argument gives branches, but the
criterion quantifies over `k -> infinity` and the branch neighbourhoods must
not shrink with `k`.

**What it would finish.**  With `atlas-a4-19243-classical-collapse` -- no
classical alignment survives collision `19243` -- and the distance floor of
`atlas-19243-centrality-forces-s3-distance`, classicalization is
contradictory, so no such `U_k` exists and `Q = L_(F_2)(1,2)^x` is not
hyperlinear.  See `nonhyperlinear-from-centralizer-product-classicalization`.

**What is already ruled out as a shortcut.**  Two `A_4` relations plus
collision `19243` do not suffice: `atlas-three-word-gap-permutation-
countermodel` is an exact twelve-point permutation model, amplifiable to every
multiplicity, in which all three words vanish.  So any proof must consume
substantially more of the thirty than three of them.
