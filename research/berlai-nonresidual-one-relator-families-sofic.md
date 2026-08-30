---
rg: 2
id: berlai-nonresidual-one-relator-families-sofic
kind: claim
title: Berlai's non-residually-solvable one-relator families are sofic
distinct_from:
  one-relator-groups-sofic: that asks for every one-relator group and remains open; this proves soficity for two explicit infinite two-generator families.
  residually-rationally-solvable-one-relator-sofic: that uses a residual hypothesis; the subfamily singled out here is not even residually solvable, so it is genuinely outside that theorem.
  one-relator-soficity-is-torsion-free-two-generator-case: that is an exact reduction with no positive conclusion; this is an outright positive theorem for explicit two-generator presentations.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

Write `x^y = y^{-1}xy` and, for noncommuting `r,w in F(a,b)`, set

```text
G_{r,w}(l,k) = <a,b | (r^l)^(r^w) = r^k>.
```

For every `n,l,k in Z \ {0}`, both

```text
G_{a,b^n}(l,k)             and
G_{a,b^{-n} a b^n}(l,k)
```

are sofic.

In particular, for `n != 0` and `l notin {0,-1}`, the group
`G_{a,b^n}(l,l+1)` is sofic but is neither residually finite nor residually
solvable. Thus these examples are not covered by
[[residually-rationally-solvable-one-relator-sofic]]. The first family settles
the problem raised by Bannon--Noblett (2010); it does not settle Pestov
Question 4.10 in full.

**ESTABLISHED.** Federico Berlai, *A new family of sofic one-relator groups*,
International Journal of Algebra and Computation 36 (2026), no. 1, 115--120,
doi:10.1142/S0218196725500444, Theorem A, Corollary B, and Theorem C; see
[[berlai-residue-class-kernel-decomposition]].
