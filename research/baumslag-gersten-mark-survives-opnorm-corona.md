---
rg: 2
id: baumslag-gersten-mark-survives-opnorm-corona
kind: claim
title: The Baumslag--Gersten generator survives an operator-norm matrix corona
distinct_from:
  higman-four-cycle-intrinsic-mf-seed: that asks whether the four cyclic Baumslag--Solitar seams force collapse; this proves that the one-seam Baumslag--Gersten closure has explicit noncollapsing operator-norm microstates.
  property-t-free-torsion-free-fp-non-mf-seed: that asks for a torsion-free finitely presented non-MF group; this rules out the Baumslag--Gersten presentation as a marked-radical seed and does not assert that the whole group is MF.
artifacts:
  - research/baumslag-gersten-primitive-shell-microstates.md
---

Let

```text
BG=<a,t | (t^(-1) a t)^(-1) a (t^(-1) a t)=a^2>.
```

There are dimensions `L_n=2*3^(n-1)` and unitary matrices

```text
A_n,T_n in U(L_n)
```

such that the displayed relator defect tends to zero in operator norm while

```text
||A_n-1||=2
```

for every `n>=2`. Consequently the generator assignment defines a
homomorphism

```text
BG -> U(product_n M_(L_n)/directSum_(||.||) M_(L_n))
```

whose value on `a` is nontrivial. In particular

```text
a notin Rad_MF(BG).
```

This is a marked noncollapse statement only. It does not claim that the
homomorphism is faithful or that `BG` is MF.

**ESTABLISHED** by
`baumslag-gersten-primitive-shell-microstates`.
