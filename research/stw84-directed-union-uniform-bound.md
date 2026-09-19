---
rg: 2
id: stw84-directed-union-uniform-bound
kind: claim
title: Uniform nuclear-dimension bounds pass from amenable subgroup exhaustions to the whole group
---

Let `G` be a countable amenable group and

```text
G_1 subset G_2 subset ... ,       union_n G_n=G
```

an increasing subgroup exhaustion.  Then

```text
C*(G)=direct_limit_n C*(G_n)
```

through injective connecting maps, and

```text
dim_nuc(C*(G)) <= liminf_n dim_nuc(C*(G_n)).
```

In particular, any uniform finite bound on the subgroup algebras is inherited
by `C*(G)`.
