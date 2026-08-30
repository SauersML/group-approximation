---
rg: 2
id: stw84-local-virtual-abelian-exhaustion-proof
kind: route
title: Exhaust by virtually abelian subgroups and close the bound with abelianization
target: stw84-locally-virtually-abelian-uniform-rank
requires:
  - stw84-directed-union-uniform-bound
  - stw84-abelianization-rank-lower-bound
---

Enumerate `G={g_1,g_2,...}` and set `G_n=<g_1,...,g_n>`.  Each `G_n` is
virtually abelian, hence amenable, so their directed union `G` is amenable.
Moreover `h(G_n)<=r`.

Chan--Lippert--Moutzouris--Weld,
[*Nuclear Dimension for Virtually Abelian
Groups*](https://arxiv.org/abs/2504.20850), prove for every finitely generated
virtually abelian group `H` that

```text
dim_nuc(C*(H))=h(H).
```

Therefore every `C*(G_n)` has nuclear dimension at most `r`.
`stw84-directed-union-uniform-bound` now gives (1).  If the rational rank of
`G_ab` is `r`, `stw84-abelianization-rank-lower-bound` supplies the reverse
inequality and hence equality.

The uniformity hypothesis is essential to this argument: finite nuclear
dimension is not preserved by an exhaustion whose stage dimensions tend to
infinity.  The conclusion also does not assert that every finite-Hirsch-length
elementary amenable group is locally virtually abelian.

