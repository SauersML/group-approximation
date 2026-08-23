---
rg: 2
id: harris-circulant-one-matrix-compiler-forces-affine-support
kind: claim
title: A one-matrix color compiler applied to the Harris circulant completion sees only affine answer support
distinct_from:
  bisynchronous-to-monomial-game-algebra-compiler: that permits arbitrary auxiliary vertices, finite phases, and full-corner or Morita encodings; this rules out only the direct one-matrix encoding of Harris's canonical circulant magic unitary.
  three-label-affine-lowering-no-go: that constructs a source whose local support-affine LCS relaxation is classically satisfiable; this classifies exactly when the direct Harris color-equality relation can represent a fixed answer support.
  finite-phase-monomial-game-algebra-dictionary: that identifies the algebra of a matrix pair once the pair is supplied; this proves an expressivity boundary for the most direct way of supplying that pair.
artifacts:
  - research/artifacts/harris-monomial-compiler-first-pass-2026-08-22.md
---

**ESTABLISHED.**  Let `K` be a finite group, written additively for notation,
and let `R subseteq K` be nonempty.  Consider the translation-invariant
bipartite relation

```text
i ~ a   iff   a-i in R.                                 (HCM1)
```

Suppose there are scalar color maps `alpha,beta:K->C` such that

```text
a-i in R   iff   alpha(i)=beta(a)                       (HCM2)
```

for every `i,a in K`.  Then `R` is a left coset of a subgroup of `K`.
Conversely every subgroup coset has such a color-equality presentation.

The same statement applies with `K=A x A` to one question pair of a
synchronous game with answer group `A`.  Harris's canonical square-magic
completion has entries

```text
u_((a,x),(i,x))=e_(a-i,x).                              (HCM3)
```

For a fixed question pair `(x,y)`, a direct ordinary weighted-matrix
isomorphism relation `uA=Bu` compares one scalar color of the source column
pair `(i,j)` with one scalar color of the target row pair `(a,b)`.  Therefore
it can retain exactly the support

```text
R_(x,y)={ (p,q): e_(p,x)e_(q,y) != 0 }                 (HCM4)
```

under `(HCM3)` only if `R_(x,y)` is an affine coset in `A x A`.

Indeed, `(HCM2)` makes the bipartite Cayley graph of `R` a disjoint union of
complete bipartite components, one for each common color.  Fix `r_0 in R`.
Every `h in R-R` shares a right neighbor with `0`, so biclique completeness
forces `h+R=R`.  Hence

```text
H={h in K:h+R=R}=R-R
```

is a subgroup and `R=r_0+H`.  Conversely, color the two sides by their
classes in `K/H`, translating one side by `r_0`.

Thus the naive pipeline

```text
arbitrary synchronous game
 -> Harris circulant magic unitary
 -> one weighted matrix pair
```

collapses precisely to affine/LCS support.  It cannot compile the nonlinear
support of the fixed non-CE BCS.  This does **not** rule out a compiler that
adds incidence vertices, uses several phase-resolved blocks, or realizes the
source as a full corner rather than through `(HCM3)`.

