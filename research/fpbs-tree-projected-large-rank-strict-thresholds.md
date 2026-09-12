---
rg: 2
id: fpbs-tree-projected-large-rank-strict-thresholds
kind: claim
title: Tree-projected Cayley graphs over a free quotient of large rank have strict thresholds
distinct_from:
  fpbs-tree-projected-cayley-graphs-strict-thresholds: that is the open root for every free rank n >= 2 with H infinite cyclic; this proves strict thresholds only when the rank is large compared with the multiplicities, by the adjacency-norm criterion, and leaves rank two open.
  fpbs-tree-projected-sphere-bubble-l2-equivalence: that is an exact criterion through critical sphere bubbles; this is a crude sufficient condition that uses no critical estimate at all.
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `H` a normal subgroup, and
`pi : Gamma -> F_n = Gamma/H` with `n >= 2` and free basis `B`. Let `S` be a
finite symmetric generating set with `pi(S) ⊆ {1} ∪ B ∪ B^(-1)`. Put

```text
v = #{g in S : pi(g) = 1},     m = max over letters t of #{g in S : pi(g) = t}.
```

If

```text
v + 2 m sqrt(2n-1) < 2n - 1,
```

then on `Cay(Gamma,S)`

```text
p_c <= 1/(2n-1) < 1/||A|| <= p_{2->2} <= p_u,
```

so `p_c < p_u`. No hypothesis is placed on `H` or on the height decorations:
asymmetric, label-dependent and non-split cases are all included.

**Thresholds.**

| multiplicities `m` | vertical generators `v` | rank covered |
|---|---|---|
| 1 (one decoration per letter) | 2 | `n >= 5` |
| 2 (e.g. decorations `{0,1}` on every letter) | 2 | `n >= 11` |

**Not new in method.** The adjacency-norm criterion `p_c < 1/||A||` is the
classical route of Benjamini–Schramm (1996) and Pak–Smirnova-Nagnibeda (2000),
and Kesten gives the norm of the tree. What this claim adds is the Schur-block
bound for arbitrary decorations. It records that the root
`fpbs-tree-projected-cayley-graphs-strict-thresholds` is open only in small
rank. At rank two the criterion fails even for the product `T_4 □ Z`: with the
Monte Carlo estimate `p_c ≈ 0.212` and `||A|| = 2 + 2 sqrt 3`, the product
`p_c ||A|| ≈ 1.16`.

Proof: `fpbs-tree-projected-large-rank-proof`.
