---
rg: 2
id: fourth-power-root-unfolding-proof
kind: route
title: Telescope the fourth power after transporting by the BS implementer
target: fourth-power-covariance-unfolds-square-root-branches
requires: []
---

First prove `(FPC2)`.  Unitary invariance and `(FPC1)` give

```text
||S-S'||_2
 =||R S R^*-R S' R^*||_2
 <=||S^4-S'^4||_2+||R S' R^*-R' S' R'^*||_2.         (FRU1)
```

The last term is at most `2||R-R'||_2`, by changing the two occurrences of
the implementer separately.  Also

```text
S^4-S'^4=(S^2-S'^2)S^2+S'^2(S^2-S'^2),               (FRU2)
```

so `||S^4-S'^4||_2<=2||S^2-S'^2||_2`.  Substitution in
`(FRU1)` proves `(FPC2)`.

For `(FPC3)`, compare the transported commutator with the fourth-power
commutator.  Direct expansion gives

```text
[C,S^4]-R[C,S]R^*
 =[C,R] S R^*+R S[C,R^*].                             (FRU3)
```

Since `||[C,R^*]||_2=||[C,R]||_2`, the right side has norm at most
`2||[C,R]||_2`.  On the other hand,

```text
[C,S^4]=[C,S^2]S^2+S^2[C,S^2],                       (FRU4)
```

whose norm is at most `2||[C,S^2]||_2`.  Unitary invariance of
`||R[C,S]R^*||_2` now proves `(FPC3)`.  Taking `C=U` and multiplying
commutators by `U^*` gives `(FPC4)`.

For the firewall corollary, `USU^*` is a square root of
`Q_p=US^2U^*`.  Hence `(FTR3)` of
`relative-first-triangle-rounding-has-an-odd-root-branch-firewall` gives
`(FPC5)`.  Rearranging `(FPC4)` and using `(FTR2)` gives `(FPC6)`.

