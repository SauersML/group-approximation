---
rg: 2
id: symmetric-double-weak-mf
kind: claim
title: Symmetric doubles of residually finite groups are weak MF
distinct_from:
  mf-positive-controls: Those are the elementary permanence facts (subgroups, residually finite groups, locally finite groups); this is an amalgamated-free-product statement whose analytic input is Shulman's C-star amalgam theorem.
  kun-thom-clifford-extension-not-weak-mf: That is a negative operator-norm result for the Clifford lamp extension; this is a positive one for the free-lamp amalgam, and the two together are what separate the lamp types.
  weakly-sofic-not-sofic: That separates weak soficity from soficity using the same family; this is the operator-norm MF statement about it.
artifacts:
  - notes/WEAK_MF_NONSOFIC_DOUBLE.md
---

Every symmetric double

```text
D = G *_Gamma G
```

of a countable residually finite group `G` over an arbitrary subgroup
`Gamma <= G` is weak MF, i.e. MF in the operator-norm
Carrion--Dadarlat--Eckhardt/Shulman norm-matrix-corona sense.

There is a finite-lamp version: for `K != 1` finite,

```text
H_K = G *_Gamma (Gamma x K)
```

is weak MF, by the Bass--Serre covering whose kernel is an amalgam of `|K|`
copies of `G` over `Gamma`, plus closure of weak MF under finite extensions.

## Why this is the load-bearing half of the lamp-type separation

Combined with `kun-thom-nonsofic-wreath` (nonsoficity, via the Kun--Thom
centralizer-normalization theorem applied to `k` centralizing `Gamma`), this
gives explicit groups that are **weak MF and nonsofic**. That separation is
exactly what `nonsofic-mechanism-mf-classification` asks for on the free-lamp
side of the mechanism.

Note the scope limit recorded in `notes/NOTEPAD.md:857-860`: this separates
weak MF from sofic. It does **not** separate Schafhauser-MF or hyperlinear
from sofic, because operator-norm separation can be supported on a subspace of
vanishing normalized rank. The point is the same one that
`weak-mf-embedding-not-reusable` makes in general.

## What it does not cover

The argument is about the **free-lamp amalgam**, not the commuting-lamp wreath.
`notes/NOTEPAD.md:30421-30423` is explicit about the boundary:

> Correction: weak MF of W is not banked. The symmetric-double proof applies
> to the free-lamp amalgam, not to the commuting-lamp wreath product. Thus
> this finite certificate is valid but stronger than the already-open weak-MF
> problem for W.

So `kun-thom-wreath-weak-mf` remains open and is not a corollary of this.
